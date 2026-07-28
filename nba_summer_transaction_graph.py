#!/usr/bin/env python3
"""Build an NBA player-movement graph from Spotrac transaction pages.

Graph model
-----------
* NBA teams are graph nodes.
* Every player movement is a directed, labelled edge from the former team to
  the new team.
* Trade edges are solid; free-agent/waiver-signing edges are dashed.
* Edge width is proportional to the player's 2026-27 base salary.
* Team positions use a crossing-aware force-directed layout that balances
  edge length, edge crossings, node/edge collisions, and angular separation.
* Team nodes use the official primary logos served by cdn.nba.com.
* Inbound-only free-agent signings are linked to the player's most recent prior
  NBA team using the previous-season tables on the Spotrac player profile.

The script writes:
  output/raw_transactions.csv
  output/movements.csv
  output/unresolved_signings.csv
  output/unresolved_salaries.csv
  output/nba_summer_transactions.png
  output/nba_summer_transactions.html

Install:
  pip install playwright beautifulsoup4 pandas networkx matplotlib pyvis pillow cairosvg
  playwright install chromium

Example:
  python nba_summer_transaction_graph.py --headed

Spotrac may change its HTML or challenge headless browsers. The parser therefore
uses player-profile links and the visible transaction text rather than fragile
CSS class names. Cached rendered HTML is kept under ./spotrac_cache.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import random
import re
import time
import unicodedata
import urllib.request
from collections import defaultdict
from dataclasses import asdict, dataclass, replace
from datetime import datetime
from pathlib import Path
from typing import Iterable
from urllib.parse import urljoin

import cairosvg
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.offsetbox import AnnotationBbox, OffsetImage
import networkx as nx
import pandas as pd
from bs4 import BeautifulSoup, Tag
from PIL import Image
from playwright.sync_api import BrowserContext, Page, sync_playwright
from pyvis.network import Network


START_DATE = "2026-04-01"
END_DATE = datetime.now().strftime("%Y-%m-%d")
SALARY_SEASON = "2026-27"
PREVIOUS_SEASON_START_YEAR = int(START_DATE[:4]) - 1
FIRST_PAGE = 1
SPOTRAC_ORIGIN = "https://www.spotrac.com"
BASE_TRANSACTIONS_URL = (
    "https://www.spotrac.com/nba/transactions/_/"
    "start/{start}/end/{end}/page/{page}"
)
BASE_FREE_AGENTS_URL = (
    "https://www.spotrac.com/nba/free-agents/_/year/2026/team/{team}"
)
BASE_SALARY_RANKINGS_URL = "https://www.spotrac.com/nba/rankings/_/year/2026"

# Team abbreviations and display names used by Spotrac.
NBA_TEAMS: dict[str, str] = {
    "ATL": "Atlanta Hawks",
    "BOS": "Boston Celtics",
    "BKN": "Brooklyn Nets",
    "CHA": "Charlotte Hornets",
    "CHI": "Chicago Bulls",
    "CLE": "Cleveland Cavaliers",
    "DAL": "Dallas Mavericks",
    "DEN": "Denver Nuggets",
    "DET": "Detroit Pistons",
    "GSW": "Golden State Warriors",
    "HOU": "Houston Rockets",
    "IND": "Indiana Pacers",
    "LAC": "LA Clippers",
    "LAL": "Los Angeles Lakers",
    "MEM": "Memphis Grizzlies",
    "MIA": "Miami Heat",
    "MIL": "Milwaukee Bucks",
    "MIN": "Minnesota Timberwolves",
    "NOP": "New Orleans Pelicans",
    "NYK": "New York Knicks",
    "OKC": "Oklahoma City Thunder",
    "ORL": "Orlando Magic",
    "PHI": "Philadelphia 76ers",
    "PHX": "Phoenix Suns",
    "POR": "Portland Trail Blazers",
    "SAC": "Sacramento Kings",
    "SAS": "San Antonio Spurs",
    "TOR": "Toronto Raptors",
    "UTA": "Utah Jazz",
    "WAS": "Washington Wizards",
}

# NBA's stable team IDs, used by the official NBA logo CDN. These are the same
# primary-logo assets displayed on https://www.nba.com/teams.
NBA_TEAM_IDS: dict[str, int] = {
    "ATL": 1610612737,
    "BOS": 1610612738,
    "CLE": 1610612739,
    "NOP": 1610612740,
    "CHI": 1610612741,
    "DAL": 1610612742,
    "DEN": 1610612743,
    "GSW": 1610612744,
    "HOU": 1610612745,
    "LAC": 1610612746,
    "LAL": 1610612747,
    "MIA": 1610612748,
    "MIL": 1610612749,
    "MIN": 1610612750,
    "BKN": 1610612751,
    "NYK": 1610612752,
    "ORL": 1610612753,
    "IND": 1610612754,
    "PHI": 1610612755,
    "PHX": 1610612756,
    "POR": 1610612757,
    "SAC": 1610612758,
    "SAS": 1610612759,
    "OKC": 1610612760,
    "TOR": 1610612761,
    "UTA": 1610612762,
    "MEM": 1610612763,
    "WAS": 1610612764,
    "DET": 1610612765,
    "CHA": 1610612766,
}

TEAM_ABBRS = set(NBA_TEAMS)
EXCLUDED_POSITIONS = {"COA", "GM"}

MONTHS = "Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Oct|Nov|Dec"
DATE_RE = re.compile(rf"\b(?:{MONTHS})\s+\d{{1,2}},\s+20\d{{2}}\b", re.I)
ACTION_RE = re.compile(
    r"\b(?:Traded|Signed|Agreed|Waived|Released|Claimed|Renounced|Drafted|"
    r"Opted?\s+Out|Option\s+(?:Exercised|Declined)|Qualifying\s+Offer)\b",
    re.I,
)
PLAYER_URL_RE = re.compile(r"/nba/player(?:s)?/", re.I)
POSITION_RE = re.compile(r"\(([A-Z][A-Z0-9/\- ]{0,9})\)")
TEAM_ABBR_RE = re.compile(r"\(([A-Z]{2,3})\)")

TRADE_RE = re.compile(
    r"Traded\s+to\s+.+?\((?P<dest>[A-Z]{2,3})\)\s+"
    r"from\s+.+?\((?P<src>[A-Z]{2,3})\)",
    re.I,
)
SIGN_DEST_RE = re.compile(
    r"(?:Signed|Agreed(?:\s+to)?)\b.*?\b(?:with|by)\s+"
    r".+?\((?P<dest>[A-Z]{2,3})\)",
    re.I,
)
CLAIM_DEST_RE = re.compile(
    r"Claimed(?:\s+off\s+waivers)?\s+by\s+.+?\((?P<dest>[A-Z]{2,3})\)",
    re.I,
)
DEPARTURE_RE = re.compile(
    r"(?:Waived|Released|Renounced)\s+by\s+.+?\((?P<team>[A-Z]{2,3})\)",
    re.I,
)
OPTION_DEPARTURE_RE = re.compile(
    r"(?:Option\s+Declined.*?(?:by|with)|Opted?\s+Out.*?(?:of|with))"
    r"\s+.+?\((?P<team>[A-Z]{2,3})\)",
    re.I,
)
DRAFT_RE = re.compile(r"\bDrafted(?:\s+by)?\b", re.I)
DRAFT_DEST_RE = re.compile(
    r"Drafted\s+by\s+.+?\((?P<team>[A-Z]{2,3})\)",
    re.I,
)

# Signing an offer sheet is not itself a completed team movement. The player
# remains with his prior team while that team has the right to match. Only a
# later record explicitly saying that the prior team declined or failed to
# match should be treated as a completed signing by the offer-sheet team.
OFFER_SHEET_RE = re.compile(r"\boffer\s+sheet\b", re.I)
OFFER_SHEET_NOT_MATCHED_RE = re.compile(
    r"(?:"
    r"\b(?:declined|failed|refused)\b.{0,80}\b(?:to\s+)?match\b"
    r"|\b(?:did\s+not|didn't|will\s+not|won't|was\s+not|wasn't)\b"
    r".{0,80}\bmatch(?:ed|ing)?\b"
    r"|\bnot\s+matched\b"
    r"|\bmatch(?:ing)?\s+period\b.{0,40}\b(?:expired|ended)\b"
    r")",
    re.I,
)


def is_nonfinal_offer_sheet_record(text: str) -> bool:
    """Return True for pending or matched offer-sheet records.

    Such records are contractual events, not completed roster movements. A
    record is allowed through only when it explicitly says the incumbent team
    did not match, allowing the player to join the offer-sheet team.
    """
    return bool(
        OFFER_SHEET_RE.search(text)
        and not OFFER_SHEET_NOT_MATCHED_RE.search(text)
    )


DRAFTED_PLAYERS_CACHE_NAME = "drafted_players.json"


@dataclass(frozen=True)
class TransactionRecord:
    player: str
    position: str
    date: str
    text: str
    player_url: str
    source_page: int

    @property
    def parsed_date(self) -> datetime:
        return datetime.strptime(self.date, "%b %d, %Y")


@dataclass(frozen=True)
class Movement:
    player: str
    source: str
    destination: str
    move_type: str  # "trade" or "free_agent"
    date: str
    description: str
    player_url: str
    salary: int | None = None
    salary_source: str = "unresolved"


@dataclass(frozen=True)
class Departure:
    date: datetime
    team: str
    description: str


def clean_text(value: str) -> str:
    return re.sub(r"\s+", " ", value or "").strip()


def canonical_player_name(name: str) -> str:
    """Normalize spelling enough to match the same player across Spotrac pages."""
    normalized = unicodedata.normalize("NFKD", name)
    normalized = "".join(ch for ch in normalized if not unicodedata.combining(ch))
    return re.sub(r"[^a-z0-9]", "", normalized.lower())


def nba_logo_url(team: str) -> str:
    """Return the official NBA primary-logo SVG URL for a team."""
    return (
        f"https://cdn.nba.com/logos/nba/{NBA_TEAM_IDS[team]}/"
        "primary/L/logo.svg"
    )


def parse_money(value: str) -> int | None:
    """Parse values such as '$18,125,000', '$2.36 million', or '$850K'."""
    text = clean_text(value).replace("USD", "")
    match = re.search(
        r"\$?\s*(?P<number>\d[\d,]*(?:\.\d+)?)\s*"
        r"(?P<unit>billion|million|thousand|[BMK])?\b",
        text,
        re.I,
    )
    if not match:
        return None

    number = float(match.group("number").replace(",", ""))
    unit = (match.group("unit") or "").lower()
    multiplier = {
        "b": 1_000_000_000,
        "billion": 1_000_000_000,
        "m": 1_000_000,
        "million": 1_000_000,
        "k": 1_000,
        "thousand": 1_000,
    }.get(unit, 1)
    return int(round(number * multiplier))


def parse_salary_from_player_html(
    html: str, season: str = SALARY_SEASON
) -> int | None:
    """Extract the player's base salary for the requested season.

    The table parser is preferred because it explicitly locates the "Base
    Salary" column. A summary-text regex is retained as a fallback because
    Spotrac occasionally changes table markup while preserving the sentence
    "In 2026-27, ... will earn a base salary of ...".
    """
    soup = BeautifulSoup(html, "html.parser")

    for table in soup.find_all("table"):
        base_salary_index: int | None = None
        for header_row in table.find_all("tr"):
            headers = [
                clean_text(cell.get_text(" ", strip=True))
                for cell in header_row.find_all(["th", "td"])
            ]
            normalized_headers = [header.lower() for header in headers]
            if "base salary" in normalized_headers:
                base_salary_index = normalized_headers.index("base salary")
                break
        if base_salary_index is None:
            continue

        for row in table.find_all("tr"):
            cells = row.find_all(["th", "td"])
            cell_text = [clean_text(cell.get_text(" ", strip=True)) for cell in cells]
            if not cell_text or not any(season in value for value in cell_text):
                continue
            if base_salary_index < len(cell_text):
                salary = parse_money(cell_text[base_salary_index])
                if salary is not None:
                    return salary

    page_text = clean_text(soup.get_text(" ", strip=True))
    summary_match = re.search(
        rf"In\s+{re.escape(season)},\s+.+?\s+will earn a base salary of\s+"
        r"(?P<salary>\$[\d,]+(?:\.\d+)?(?:\s*(?:million|thousand|[BMK]))?)",
        page_text,
        re.I,
    )
    if summary_match:
        return parse_money(summary_match.group("salary"))

    return None


def estimate_annual_salary_from_description(description: str) -> int | None:
    """Estimate annual salary from a newly signed contract description.

    This is a fallback for contracts not yet reflected on a player's profile.
    It divides the stated total contract value by the stated number of years.
    The estimate is intentionally marked separately in the output CSV.
    """
    match = re.search(
        r"(?:Signed|Agreed(?:\s+to)?)\b.*?"
        r"(?:(?P<years>\d+)\s*(?:year|yr)s?\s*[,/-]?\s*)?"
        r"(?P<value>\$\s*\d[\d,]*(?:\.\d+)?\s*"
        r"(?:billion|million|thousand|[BMK])?)\b",
        description,
        re.I,
    )
    if not match:
        return None

    total_value = parse_money(match.group("value"))
    if total_value is None:
        return None
    years = int(match.group("years") or 1)
    return int(round(total_value / max(years, 1)))


def format_salary(salary: int | None) -> str:
    if salary is None:
        return "Salary unavailable"
    if salary >= 1_000_000:
        return f"${salary / 1_000_000:.1f}M"
    if salary >= 1_000:
        return f"${salary / 1_000:.0f}K"
    return f"${salary:,}"


def position_from_text(text: str, player: str) -> str:
    # Prefer the parenthesized token immediately following the player name.
    match = re.search(re.escape(player) + r"\s*\(([^)]+)\)", text, re.I)
    if match:
        return clean_text(match.group(1)).upper()

    # Fallback: first plausible position token, excluding NBA team abbreviations.
    for match in POSITION_RE.finditer(text):
        value = clean_text(match.group(1)).upper()
        if value not in TEAM_ABBRS:
            return value
    return ""


def name_from_anchor(anchor: Tag, names_by_href: dict[str, str]) -> str:
    href = anchor.get("href", "")
    if href in names_by_href:
        return names_by_href[href]
    return ""


def infer_anchor_name(anchor: Tag) -> str:
    candidates = [
        clean_text(anchor.get_text(" ", strip=True)),
        clean_text(anchor.get("title", "")),
        clean_text(anchor.get("aria-label", "")),
    ]
    image = anchor.find("img")
    if image:
        candidates.extend(
            [clean_text(image.get("alt", "")), clean_text(image.get("title", ""))]
        )

    candidates = [re.sub(r"^Image\s+", "", value, flags=re.I) for value in candidates]
    candidates = [value for value in candidates if value]
    return max(candidates, key=len, default="")


def player_anchors(soup: BeautifulSoup) -> list[Tag]:
    return [
        anchor
        for anchor in soup.find_all("a", href=True)
        if PLAYER_URL_RE.search(str(anchor.get("href", "")))
    ]


def find_transaction_container(anchor: Tag) -> Tag | None:
    """Find the smallest ancestor containing one complete transaction record."""
    parents = [parent for parent in anchor.parents if isinstance(parent, Tag)]

    # Prefer semantic row/card containers before falling back to any ancestor.
    for parent in parents:
        classes = " ".join(parent.get("class", []))
        is_row_like = (
            parent.name in {"tr", "li", "article"}
            or re.search(r"(?:transaction|data-row|table-row|list-group-item|card)", classes, re.I)
        )
        if not is_row_like:
            continue
        text = clean_text(parent.get_text(" ", strip=True))
        if len(text) <= 3500 and DATE_RE.search(text) and ACTION_RE.search(text):
            return parent

    for parent in parents:
        text = clean_text(parent.get_text(" ", strip=True))
        if len(text) > 3500:
            break
        if DATE_RE.search(text) and ACTION_RE.search(text):
            return parent
    return None


def parse_transaction_html(html: str, source_page: int) -> list[TransactionRecord]:
    soup = BeautifulSoup(html, "html.parser")
    anchors = player_anchors(soup)

    # Player images and player names often use separate anchors with the same URL.
    names_by_href: dict[str, str] = {}
    for anchor in anchors:
        href = str(anchor.get("href", ""))
        candidate = infer_anchor_name(anchor)
        if candidate and len(candidate) > len(names_by_href.get(href, "")):
            names_by_href[href] = candidate

    records: list[TransactionRecord] = []
    seen: set[tuple[str, str, str]] = set()

    for anchor in anchors:
        player = name_from_anchor(anchor, names_by_href)
        if not player:
            continue

        container = find_transaction_container(anchor)
        if container is None:
            continue

        text = clean_text(container.get_text(" ", strip=True))
        date_match = DATE_RE.search(text)
        if not date_match:
            continue

        position = position_from_text(text, player)
        if position in EXCLUDED_POSITIONS:
            continue

        key = (canonical_player_name(player), date_match.group(0), text)
        if key in seen:
            continue
        seen.add(key)

        records.append(
            TransactionRecord(
                player=player,
                position=position,
                date=date_match.group(0),
                text=text,
                player_url=str(anchor.get("href", "")),
                source_page=source_page,
            )
        )

    return records


def parse_player_names_from_free_agent_html(html: str) -> set[str]:
    """Return normalized player names shown in the main free-agent results table."""
    soup = BeautifulSoup(html, "html.parser")

    # Avoid unrelated player links in navigation, news or recommendation panels.
    anchors = [
        anchor
        for anchor in soup.select('table a[href]')
        if PLAYER_URL_RE.search(str(anchor.get("href", "")))
    ]
    if not anchors:
        main = soup.find("main")
        anchors = player_anchors(main if isinstance(main, BeautifulSoup) else soup)
        if main is not None:
            anchors = [
                anchor
                for anchor in main.find_all("a", href=True)
                if PLAYER_URL_RE.search(str(anchor.get("href", "")))
            ]

    names: set[str] = set()
    for anchor in anchors:
        name = infer_anchor_name(anchor)
        if name:
            names.add(canonical_player_name(name))
    return names


def parse_salary_rankings_html(html: str) -> dict[str, int]:
    """Parse player base salaries from Spotrac's season rankings table."""
    soup = BeautifulSoup(html, "html.parser")
    salaries: dict[str, int] = {}

    for table in soup.find_all("table"):
        salary_index: int | None = None
        for header_row in table.find_all("tr"):
            headers = [
                clean_text(cell.get_text(" ", strip=True)).lower()
                for cell in header_row.find_all(["th", "td"])
            ]
            matching_indices = [
                index
                for index, header in enumerate(headers)
                if header in {"base salary", "salary"}
            ]
            if matching_indices:
                salary_index = matching_indices[0]
                break
        if salary_index is None:
            continue

        for row in table.find_all("tr"):
            cells = row.find_all(["th", "td"])
            if salary_index >= len(cells):
                continue
            anchor = next(
                (
                    candidate
                    for candidate in row.find_all("a", href=True)
                    if PLAYER_URL_RE.search(str(candidate.get("href", "")))
                ),
                None,
            )
            if anchor is None:
                continue
            player = infer_anchor_name(anchor)
            salary = parse_money(cells[salary_index].get_text(" ", strip=True))
            if player and salary is not None:
                salaries[canonical_player_name(player)] = salary

    return salaries



def _season_start_year(value: str) -> int | None:
    """Return the starting year from values such as '2025' or '2025-26'."""
    match = re.search(r"\b(20\d{2})(?:\s*[-–/]\s*(?:20)?\d{2})?\b", value)
    return int(match.group(1)) if match else None


def _team_hints_from_fragment(fragment: Tag) -> list[str]:
    """Extract NBA team abbreviations from a table cell or similar HTML fragment.

    Spotrac frequently represents a team only as an image, so this checks visible
    text, accessibility attributes, URLs, official NBA team IDs, and full names.
    Results preserve document order and contain no duplicates.
    """
    found: list[str] = []

    def add(team: str | None) -> None:
        team = valid_team(team)
        if team and team not in found:
            found.append(team)

    short_aliases = {
        "GS": "GSW",
        "NY": "NYK",
        "NO": "NOP",
        "OK": "OKC",
        "SA": "SAS",
    }

    id_to_team = {str(team_id): team for team, team_id in NBA_TEAM_IDS.items()}
    name_aliases: dict[str, str] = {}
    for team, full_name in NBA_TEAMS.items():
        normalized = re.sub(r"[^a-z0-9]", "", full_name.lower())
        name_aliases[normalized] = team
    # Common variants that may differ from NBA_TEAMS display names.
    name_aliases.update(
        {
            "losangelesclippers": "LAC",
            "laclippers": "LAC",
            "losangeleslakers": "LAL",
            "goldenstatewarriors": "GSW",
            "neworleanspelicans": "NOP",
            "oklahomacitythunder": "OKC",
            "portlandtrailblazers": "POR",
            "sanantoniospurs": "SAS",
        }
    )

    elements: list[Tag] = [fragment, *fragment.find_all(True)]
    for element in elements:
        values = [clean_text(element.get_text(" ", strip=True))]
        for attribute in (
            "alt",
            "title",
            "aria-label",
            "data-team",
            "data-abbr",
            "href",
            "src",
        ):
            raw_value = element.get(attribute)
            if isinstance(raw_value, str):
                values.append(clean_text(raw_value))

        for value in values:
            if not value:
                continue

            upper_value = value.upper()
            for short_code, team in short_aliases.items():
                if re.search(rf"(?<![A-Z]){re.escape(short_code)}(?![A-Z])", upper_value):
                    add(team)

            for match in re.finditer(r"(?<![A-Z])([A-Z]{2,3})(?![A-Z])", value.upper()):
                add(match.group(1))

            normalized_value = re.sub(r"[^a-z0-9]", "", value.lower())
            for normalized_name, team in name_aliases.items():
                if normalized_name and normalized_name in normalized_value:
                    add(team)

            for team_id, team in id_to_team.items():
                if team_id in value:
                    add(team)

            # Team-specific URLs commonly contain /team/lac or /team/lac/.
            url_match = re.search(r"/team/([a-z]{2,3})(?:/|$|\?)", value, re.I)
            if url_match:
                add(url_match.group(1).upper())

    return found


def _profile_transaction_chunks(html: str) -> list[tuple[datetime, str]]:
    """Return dated transaction descriptions from a Spotrac player profile.

    Spotrac can contain several transactions on the same day. Keeping each
    description separate lets us reconstruct draft-day chains such as
    NYK -> HOU -> LAC without relying on the visual/DOM order of equal-date rows.
    """
    soup = BeautifulSoup(html, "html.parser")
    page_text = clean_text(soup.get_text(" ", strip=True))
    date_matches = list(DATE_RE.finditer(page_text))
    chunks: list[tuple[datetime, str]] = []

    for index, date_match in enumerate(date_matches):
        try:
            event_date = datetime.strptime(date_match.group(0), "%b %d, %Y")
        except ValueError:
            continue
        next_start = (
            date_matches[index + 1].start()
            if index + 1 < len(date_matches)
            else len(page_text)
        )
        event_text = page_text[
            date_match.start() : min(next_start, date_match.start() + 1200)
        ]
        chunks.append((event_date, event_text))

    return chunks


def profile_shows_drafted_in_year(html: str, year: int) -> bool:
    """Return True when the profile records that the player was drafted in year."""
    return any(
        event_date.year == year and DRAFT_RE.search(event_text)
        for event_date, event_text in _profile_transaction_chunks(html)
    )


def _terminal_team_from_same_day_trades(
    trades: list[tuple[str, str]],
) -> str | None:
    """Find the terminal team in one or more same-day trade chains.

    For example, [('HOU', 'LAC'), ('NYK', 'HOU')] resolves to LAC regardless
    of the order in which Spotrac displays those two events.
    """
    if not trades:
        return None

    sources = {source for source, _destination in trades}
    destinations = {destination for _source, destination in trades}
    terminal_destinations = destinations - sources
    if len(terminal_destinations) == 1:
        return next(iter(terminal_destinations))

    # Ambiguous/multiple chains: walk every possible chain and keep the longest.
    outgoing: dict[str, list[str]] = defaultdict(list)
    for source, destination in trades:
        if destination not in outgoing[source]:
            outgoing[source].append(destination)

    starting_teams = sources - destinations or sources
    best_terminal: str | None = None
    best_length = -1
    for start_team in starting_teams:
        stack: list[tuple[str, int, frozenset[tuple[str, str]]]] = [
            (start_team, 0, frozenset())
        ]
        while stack:
            team, length, used = stack.pop()
            next_moves = [
                (team, destination)
                for destination in outgoing.get(team, [])
                if (team, destination) not in used
            ]
            if not next_moves:
                if length > best_length:
                    best_terminal = team
                    best_length = length
                continue
            for edge in next_moves:
                stack.append(
                    (edge[1], length + 1, used | {edge})
                )

    return best_terminal


def _latest_team_from_profile_transactions(
    html: str,
    signing_date: datetime,
) -> str | None:
    """Infer the player's last team from the profile's season/team tables.

    Spotrac's career-earnings and season-stat tables contain the last completed
    season's team without relying on the partial transaction history. That data
    is preferred. Transaction history remains a fallback only when the tables do
    not provide a usable team row.
    """
    soup = BeautifulSoup(html, "html.parser")
    season_rows: list[tuple[int, list[str]]] = []

    for table in soup.find_all("table"):
        year_index: int | None = None
        team_index: int | None = None

        for row in table.find_all("tr"):
            cells = row.find_all(["th", "td"])
            headers = [clean_text(cell.get_text(" ", strip=True)).lower() for cell in cells]
            if "year" not in headers:
                continue
            possible_team_indices = [
                index
                for index, header in enumerate(headers)
                if header in {"team", "team(s)", "teams"}
            ]
            if possible_team_indices:
                year_index = headers.index("year")
                team_index = possible_team_indices[0]
                break

        if year_index is None or team_index is None:
            continue

        for row in table.find_all("tr"):
            cells = row.find_all(["th", "td"])
            if max(year_index, team_index) >= len(cells):
                continue
            season = _season_start_year(clean_text(cells[year_index].get_text(" ", strip=True)))
            if season is None or season >= signing_date.year:
                continue
            row_teams = _team_hints_from_fragment(cells[team_index])
            if row_teams:
                season_rows.append((season, row_teams))

    if season_rows:
        latest_season = max(season for season, _teams in season_rows)
        latest_season_rows = [
            teams for season, teams in season_rows if season == latest_season
        ]
        for teams in reversed(latest_season_rows):
            if teams:
                return teams[-1]

    dated_events: list[tuple[datetime, str, str | None, str | None]] = []
    for event_date, event_text in _profile_transaction_chunks(html):
        if event_date >= signing_date:
            continue
        if is_nonfinal_offer_sheet_record(event_text):
            # A pending offer sheet, or one that was matched, did not change
            # the player's team and must not become the inferred prior team.
            continue

        trade_match = TRADE_RE.search(event_text)
        sign_match = SIGN_DEST_RE.search(event_text)
        claim_match = CLAIM_DEST_RE.search(event_text)
        draft_match = DRAFT_DEST_RE.search(event_text)

        if trade_match:
            dated_events.append(
                (
                    event_date,
                    "trade",
                    valid_team(trade_match.group("src")),
                    valid_team(trade_match.group("dest")),
                )
            )
        elif sign_match:
            dated_events.append(
                (
                    event_date,
                    "arrival",
                    None,
                    valid_team(sign_match.group("dest")),
                )
            )
        elif claim_match:
            dated_events.append(
                (
                    event_date,
                    "arrival",
                    None,
                    valid_team(claim_match.group("dest")),
                )
            )
        elif draft_match:
            dated_events.append(
                (
                    event_date,
                    "draft",
                    None,
                    valid_team(draft_match.group("team")),
                )
            )
        else:
            for regex in (DEPARTURE_RE, OPTION_DEPARTURE_RE):
                departure_match = regex.search(event_text)
                if departure_match:
                    dated_events.append(
                        (
                            event_date,
                            "departure",
                            valid_team(departure_match.group("team")),
                            None,
                        )
                    )
                    break

    if not dated_events:
        return None

    latest_date = max(event[0] for event in dated_events)
    latest_events = [event for event in dated_events if event[0] == latest_date]

    arrival_destinations = [
        destination
        for _date, kind, _source, destination in latest_events
        if kind in {"arrival", "draft"} and destination
    ]
    trades = [
        (source, destination)
        for _date, kind, source, destination in latest_events
        if kind == "trade" and source and destination
    ]

    trade_terminal = _terminal_team_from_same_day_trades(trades)
    if trade_terminal:
        return trade_terminal
    if arrival_destinations:
        return arrival_destinations[0]

    departure_teams = [
        source
        for _date, kind, source, _destination in latest_events
        if kind == "departure" and source
    ]
    return departure_teams[0] if departure_teams else None


def parse_previous_team_from_player_html(
    html: str,
    signing_date: datetime,
    latest_allowed_season: int = PREVIOUS_SEASON_START_YEAR,
) -> str | None:
    """Return the NBA team the player most recently played for before signing.

    The preferred source is the most recent Spotrac year/team table at or before
    the previous NBA season. If that row lists multiple teams, profile transaction
    history is used to identify the final one. Transaction history also serves as
    a fallback for players whose statistics/earnings table is incomplete.
    """
    soup = BeautifulSoup(html, "html.parser")
    teams_by_season: dict[int, list[str]] = defaultdict(list)

    for table in soup.find_all("table"):
        year_index: int | None = None
        team_index: int | None = None

        for row in table.find_all("tr"):
            cells = row.find_all(["th", "td"])
            headers = [clean_text(cell.get_text(" ", strip=True)).lower() for cell in cells]
            if "year" not in headers:
                continue
            possible_team_indices = [
                index
                for index, header in enumerate(headers)
                if header in {"team", "team(s)", "teams"}
            ]
            if possible_team_indices:
                year_index = headers.index("year")
                team_index = possible_team_indices[0]
                break

        if year_index is None or team_index is None:
            continue

        for row in table.find_all("tr"):
            cells = row.find_all(["th", "td"])
            if max(year_index, team_index) >= len(cells):
                continue
            season = _season_start_year(clean_text(cells[year_index].get_text(" ", strip=True)))
            if season is None or season > latest_allowed_season:
                continue

            row_teams = _team_hints_from_fragment(cells[team_index])
            for team in row_teams:
                if team not in teams_by_season[season]:
                    teams_by_season[season].append(team)

    history_team = _latest_team_from_profile_transactions(html, signing_date)
    if teams_by_season:
        most_recent_season = max(teams_by_season)
        season_teams = teams_by_season[most_recent_season]
        if history_team in season_teams:
            return history_team
        if len(season_teams) == 1:
            return season_teams[0]
        if season_teams:
            # Spotrac generally places teams chronologically within a multi-team cell.
            return season_teams[-1]

    return history_team


def drafted_player_keys(records: Iterable[TransactionRecord]) -> set[str]:
    """Return normalized player names for players who were drafted this year."""
    return {
        canonical_player_name(record.player)
        for record in records
        if DRAFT_RE.search(record.text)
    }


def drafted_players_cache_path(cache_dir: Path) -> Path:
    return cache_dir / DRAFTED_PLAYERS_CACHE_NAME


def load_drafted_players(cache_dir: Path) -> set[str]:
    path = drafted_players_cache_path(cache_dir)
    if not path.exists():
        return set()
    raw = json.loads(path.read_text(encoding="utf-8"))
    return {canonical_player_name(str(player)) for player in raw if str(player).strip()}


def load_drafted_players_from_raw_transactions(output_dir: Path) -> set[str]:
    path = output_dir / "raw_transactions.csv"
    if not path.exists():
        return set()

    frame = pd.read_csv(path, usecols=["player", "text"], dtype=str).fillna("")
    return {
        canonical_player_name(str(player))
        for player, text in frame[["player", "text"]].itertuples(index=False, name=None)
        if DRAFT_RE.search(str(text))
    }


def load_cached_transaction_records(output_dir: Path) -> list[TransactionRecord]:
    """Load the previously saved raw transaction records, if available."""
    path = output_dir / "raw_transactions.csv"
    if not path.exists():
        return []

    try:
        frame = pd.read_csv(path, dtype=str).fillna("")
    except (OSError, pd.errors.EmptyDataError, pd.errors.ParserError) as error:
        print(f"Could not load cached transactions from {path}: {error}")
        return []

    required_columns = {
        "player",
        "position",
        "date",
        "text",
        "player_url",
        "source_page",
    }
    missing_columns = required_columns - set(frame.columns)
    if missing_columns:
        print(
            f"Ignoring cached transactions in {path}: missing columns "
            f"{sorted(missing_columns)}"
        )
        return []

    records: list[TransactionRecord] = []
    for row in frame.to_dict("records"):
        try:
            source_page = int(float(row["source_page"]))
            record = TransactionRecord(
                player=str(row["player"]),
                position=str(row["position"]),
                date=str(row["date"]),
                text=str(row["text"]),
                player_url=str(row["player_url"]),
                source_page=source_page,
            )
            # Validate the date while loading so a malformed row cannot break
            # incremental fetching for the rest of the cached history.
            _ = record.parsed_date
        except (TypeError, ValueError) as error:
            print(f"Skipping malformed cached transaction row: {error}")
            continue
        records.append(record)

    return records


def determine_transaction_start_date(
    cached_records: Iterable[TransactionRecord],
    refresh: bool,
) -> str:
    """Use the latest cached transaction date unless a full refresh was requested."""
    if refresh:
        print(f"Full refresh requested; fetching transactions from {START_DATE}")
        return START_DATE

    cached_records = list(cached_records)
    if not cached_records:
        print(f"No cached transaction rows found; fetching from {START_DATE}")
        return START_DATE

    latest_cached_date = max(record.parsed_date for record in cached_records)
    configured_start = datetime.strptime(START_DATE, "%Y-%m-%d")
    effective_start = max(latest_cached_date, configured_start)
    print(
        f"Latest cached transaction date: {latest_cached_date:%Y-%m-%d}; "
        f"fetching transactions from {effective_start:%Y-%m-%d}"
    )
    return effective_start.strftime("%Y-%m-%d")


def merge_transaction_records(
    cached_records: Iterable[TransactionRecord],
    fetched_records: Iterable[TransactionRecord],
    replace_from_date: str,
) -> list[TransactionRecord]:
    """Merge a fresh transaction tail with the previously saved history."""
    cutoff = datetime.strptime(replace_from_date, "%Y-%m-%d")

    # Replace the first fetched day rather than merely appending it. This allows
    # same-day additions and corrected descriptions to supersede cached rows.
    combined = [
        record for record in cached_records if record.parsed_date < cutoff
    ]
    combined.extend(fetched_records)

    unique: dict[tuple[str, str, str], TransactionRecord] = {}
    for record in combined:
        key = (canonical_player_name(record.player), record.date, record.text)
        unique[key] = record

    return sorted(
        unique.values(),
        key=lambda record: (
            record.parsed_date,
            canonical_player_name(record.player),
            record.text,
        ),
    )


def save_drafted_players(cache_dir: Path, players: Iterable[str]) -> None:
    path = drafted_players_cache_path(cache_dir)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(sorted({canonical_player_name(player) for player in players}), indent=2),
        encoding="utf-8",
    )


def fetch_profile_html(
    page: Page,
    profile_url: str,
    cache_dir: Path,
    refresh: bool,
    request_pause: float,
    profile_html_cache: dict[str, str],
) -> str:
    cached = profile_html_cache.get(profile_url)
    if cached is not None:
        return cached

    html = fetch_rendered_html(page, profile_url, cache_dir, refresh, request_pause)
    profile_html_cache[profile_url] = html
    return html


def scrape_previous_season_sources(
    page: Page,
    unresolved_signings: list[dict[str, str]],
    cache_dir: Path,
    refresh: bool,
    request_pause: float,
    profile_html_cache: dict[str, str],
    refresh_player_keys: set[str] | None = None,
) -> tuple[dict[str, str], set[str]]:
    """Resolve inbound-only signings and identify current-year drafted players.

    Returns:
        (previous_team_by_player, drafted_player_keys)

    Drafted players are not assigned a previous NBA team and are excluded from
    the movement graph entirely.
    """
    source_map: dict[str, str] = {}
    drafted_players: set[str] = set()
    unique_players: dict[str, dict[str, str]] = {}
    for item in unresolved_signings:
        player_key = canonical_player_name(item.get("player", ""))
        if player_key:
            unique_players.setdefault(player_key, item)

    for player_key, item in unique_players.items():
        player = item.get("player", "")
        profile_url = canonical_spotrac_player_url(item.get("player_url", ""))
        if not profile_url:
            print(f"  previous-team lookup skipped for {player}: no player profile URL")
            continue

        try:
            signing_date = datetime.strptime(item["date"], "%b %d, %Y")
            html = fetch_profile_html(
                page,
                profile_url,
                cache_dir,
                refresh or bool(refresh_player_keys and player_key in refresh_player_keys),
                request_pause,
                profile_html_cache,
            )

            if profile_shows_drafted_in_year(html, signing_date.year):
                drafted_players.add(player_key)
                print(f"  {player}: drafted in {signing_date.year}; excluding rookie")
                continue

            source = parse_previous_team_from_player_html(html, signing_date)
        except Exception as error:
            print(f"  previous-team lookup failed for {player}: {error}")
            continue

        destination = valid_team(item.get("destination"))
        if source and source != destination:
            source_map[player_key] = source
            print(f"  {player}: previous team {source}")
        elif source == destination:
            print(
                f"  {player}: previous team equals destination ({destination}); "
                "treating as re-signing"
            )
        else:
            print(f"  {player}: previous team unresolved")

    return source_map, drafted_players


def cache_path(cache_dir: Path, url: str) -> Path:
    digest = hashlib.sha256(url.encode("utf-8")).hexdigest()[:16]
    return cache_dir / f"{digest}.html"


def accept_cookie_banner(page: Page) -> None:
    for label in ("Accept", "Accept All", "I Agree", "Agree"):
        try:
            button = page.get_by_role("button", name=re.compile(rf"^{re.escape(label)}$", re.I))
            if button.count() > 0 and button.first.is_visible():
                button.first.click(timeout=1500)
                return
        except Exception:
            pass


def fetch_rendered_html(
    page: Page,
    url: str,
    cache_dir: Path,
    refresh: bool,
    request_pause: float,
) -> str:
    cache_dir.mkdir(parents=True, exist_ok=True)
    cached = cache_path(cache_dir, url)
    if cached.exists() and not refresh:
        return cached.read_text(encoding="utf-8")

    print(f"Fetching {url}")
    page.goto(url, wait_until="domcontentloaded", timeout=90_000)
    page.wait_for_timeout(2500)
    accept_cookie_banner(page)
    page.wait_for_timeout(750)

    body_text = clean_text(page.locator("body").inner_text(timeout=15_000))
    blocked_markers = (
        "access denied",
        "verify you are human",
        "checking your browser",
        "just a moment",
        "captcha",
    )
    if any(marker in body_text.lower() for marker in blocked_markers):
        raise RuntimeError(
            "Spotrac presented an anti-bot page. Re-run with --headed and, if "
            "needed, --user-data-dir ./browser_profile so the browser session "
            "can retain cookies after you complete the challenge."
        )

    html = page.content()
    cached.write_text(html, encoding="utf-8")
    time.sleep(request_pause)
    return html


def scrape_transactions(
    page: Page,
    cache_dir: Path,
    refresh: bool,
    request_pause: float,
    start_date: str,
    end_date: str,
) -> list[TransactionRecord]:
    records: list[TransactionRecord] = []
    page_number = FIRST_PAGE
    previous_page_signature: tuple[tuple[str, str, str, str, str], ...] | None = None
    while True:
        url = BASE_TRANSACTIONS_URL.format(
            start=start_date, end=end_date, page=page_number
        )
        html = fetch_rendered_html(page, url, cache_dir, refresh, request_pause)
        page_records = parse_transaction_html(html, source_page=page_number)
        print(f"  parsed {len(page_records)} transaction rows from page {page_number}")
        if not page_records:
            break
        current_page_signature = tuple(
            (record.player, record.position, record.date, record.text, record.player_url)
            for record in page_records
        )
        if previous_page_signature is not None and current_page_signature == previous_page_signature:
            print(f"  page {page_number} matches the previous page; stopping pagination")
            break
        records.extend(page_records)
        previous_page_signature = current_page_signature
        page_number += 1

    # Remove duplicates that can occur around pagination boundaries.
    unique: dict[tuple[str, str, str], TransactionRecord] = {}
    for record in records:
        key = (canonical_player_name(record.player), record.date, record.text)
        unique[key] = record
    return list(unique.values())


def candidate_signing_players(
    records: Iterable[TransactionRecord],
    excluded_players: set[str] | None = None,
) -> set[str]:
    result = set()
    for record in records:
        player_key = canonical_player_name(record.player)
        if excluded_players and player_key in excluded_players:
            continue
        if is_nonfinal_offer_sheet_record(record.text):
            continue
        if SIGN_DEST_RE.search(record.text) or CLAIM_DEST_RE.search(record.text):
            result.add(player_key)
    return result


def scrape_free_agent_sources(
    page: Page,
    candidate_players: set[str],
    cache_dir: Path,
    refresh: bool,
    request_pause: float,
) -> dict[str, str]:
    """Map a signed player's normalized name to his previous NBA team.

    Spotrac's team-specific 2026 free-agent page is keyed by the player's former
    team. Therefore, finding a player on /team/LAL identifies LAL as his source.
    """
    source_map: dict[str, str] = {}

    for team in NBA_TEAMS:
        unresolved = candidate_players - source_map.keys()
        if not unresolved:
            break

        url = BASE_FREE_AGENTS_URL.format(team=team.lower())
        html = fetch_rendered_html(page, url, cache_dir, refresh, request_pause)
        names = parse_player_names_from_free_agent_html(html)
        matched = unresolved & names
        for player_key in matched:
            source_map[player_key] = team
        if matched:
            print(f"  {team}: matched {len(matched)} signed player(s)")

    return source_map


def scrape_salary_rankings(
    page: Page,
    cache_dir: Path,
    refresh: bool,
    request_pause: float,
) -> dict[str, int]:
    """Fetch Spotrac's 2026 base-salary rankings as a bulk salary lookup."""
    try:
        html = fetch_rendered_html(
            page,
            BASE_SALARY_RANKINGS_URL,
            cache_dir,
            refresh,
            request_pause,
        )
        salaries = parse_salary_rankings_html(html)
        print(f"Parsed {len(salaries)} salaries from Spotrac rankings")
        return salaries
    except Exception as error:
        print(f"Salary rankings lookup failed; falling back to player pages: {error}")
        return {}


def canonical_spotrac_player_url(player_url: str) -> str:
    """Convert a relative or subsection player link to the main profile URL."""
    if not player_url:
        return ""
    absolute = urljoin(SPOTRAC_ORIGIN, player_url)
    return re.sub(
        r"/nba/player/(?:transactions|cash-earnings|career-earnings|market-value)/_/id/",
        "/nba/player/_/id/",
        absolute,
        flags=re.I,
    )


def load_salary_overrides(path: Path | None) -> dict[str, int]:
    """Load optional {"Player Name": 18125000} salary corrections."""
    if path is None:
        return {}
    raw = json.loads(path.read_text(encoding="utf-8"))
    result: dict[str, int] = {}
    for player, value in raw.items():
        salary = parse_money(str(value)) if isinstance(value, str) else int(value)
        if salary is None or salary <= 0:
            raise ValueError(f"Salary override must be positive for {player}: {value}")
        result[canonical_player_name(str(player))] = salary
    return result


def scrape_movement_salaries(
    page: Page,
    movements: list[Movement],
    salary_overrides: dict[str, int],
    rankings_salaries: dict[str, int],
    cache_dir: Path,
    refresh: bool,
    request_pause: float,
    profile_html_cache: dict[str, str],
    refresh_player_keys: set[str] | None = None,
) -> tuple[list[Movement], list[dict[str, str]]]:
    """Attach 2026-27 base salaries to movements.

    The bulk Spotrac salary ranking is preferred, followed by the player's
    profile. If neither is updated yet, use an annualized estimate from a newly
    signed contract's transaction text.
    """
    salary_data: dict[str, tuple[int | None, str]] = {}

    unique_movements: dict[str, Movement] = {}
    for movement in movements:
        unique_movements.setdefault(canonical_player_name(movement.player), movement)

    for player_key, movement in unique_movements.items():
        if player_key in salary_overrides:
            salary_data[player_key] = (salary_overrides[player_key], "override")
            continue

        if player_key in rankings_salaries:
            salary = rankings_salaries[player_key]
            salary_data[player_key] = (
                salary,
                f"Spotrac {SALARY_SEASON} salary rankings",
            )
            print(f"  {movement.player}: {format_salary(salary)}")
            continue

        salary: int | None = None
        profile_url = canonical_spotrac_player_url(movement.player_url)
        if profile_url:
            try:
                html = fetch_profile_html(
                    page,
                    profile_url,
                    cache_dir,
                    refresh or bool(refresh_player_keys and player_key in refresh_player_keys),
                    request_pause,
                    profile_html_cache,
                )
                salary = parse_salary_from_player_html(html, SALARY_SEASON)
            except Exception as error:
                print(f"  salary lookup failed for {movement.player}: {error}")

        if salary is not None:
            salary_data[player_key] = (salary, f"Spotrac {SALARY_SEASON} base salary")
            print(f"  {movement.player}: {format_salary(salary)}")
            continue

        estimated = estimate_annual_salary_from_description(movement.description)
        if estimated is not None:
            salary_data[player_key] = (estimated, "estimated annual contract value")
            print(
                f"  {movement.player}: {format_salary(estimated)} "
                "(annualized transaction estimate)"
            )
        else:
            salary_data[player_key] = (None, "unresolved")
            print(f"  {movement.player}: salary unresolved")

    enriched: list[Movement] = []
    unresolved: list[dict[str, str]] = []
    for movement in movements:
        salary, source = salary_data[canonical_player_name(movement.player)]
        enriched.append(replace(movement, salary=salary, salary_source=source))
        if salary is None:
            unresolved.append(
                {
                    "player": movement.player,
                    "date": movement.date,
                    "source": movement.source,
                    "destination": movement.destination,
                    "player_url": canonical_spotrac_player_url(movement.player_url),
                    "suggestion": (
                        "Add the 2026-27 salary in dollars to --salary-overrides, "
                        'for example: {"Player Name": 18125000}'
                    ),
                }
            )

    return enriched, unresolved


def valid_team(abbreviation: str | None) -> str | None:
    if not abbreviation:
        return None
    abbreviation = abbreviation.upper()
    return abbreviation if abbreviation in TEAM_ABBRS else None


def extract_departure(record: TransactionRecord) -> str | None:
    for regex in (DEPARTURE_RE, OPTION_DEPARTURE_RE):
        match = regex.search(record.text)
        if match:
            return valid_team(match.group("team"))
    return None


def load_overrides(path: Path | None) -> dict[str, str]:
    """Load optional {"Player Name": "OLD_TEAM_ABBR"} corrections."""
    if path is None:
        return {}
    raw = json.loads(path.read_text(encoding="utf-8"))
    result: dict[str, str] = {}
    for player, team in raw.items():
        normalized_team = valid_team(str(team))
        if normalized_team is None:
            raise ValueError(f"Unknown NBA team abbreviation in overrides: {team}")
        result[canonical_player_name(str(player))] = normalized_team
    return result


def latest_departure_before(
    departures: list[Departure], signing_date: datetime
) -> Departure | None:
    eligible = [departure for departure in departures if departure.date <= signing_date]
    return max(eligible, key=lambda item: item.date, default=None)


def build_movements(
    records: list[TransactionRecord],
    free_agent_sources: dict[str, str],
    overrides: dict[str, str],
    drafted_players: set[str] | None = None,
) -> tuple[list[Movement], list[dict[str, str]]]:
    departures: dict[str, list[Departure]] = defaultdict(list)

    for record in records:
        team = extract_departure(record)
        if team:
            departures[canonical_player_name(record.player)].append(
                Departure(record.parsed_date, team, record.text)
            )

    movements: list[Movement] = []
    unresolved: list[dict[str, str]] = []
    seen: set[tuple[str, str, str, str, str]] = set()

    for record in sorted(records, key=lambda item: item.parsed_date):
        player_key = canonical_player_name(record.player)

        if drafted_players and player_key in drafted_players:
            continue

        trade_match = TRADE_RE.search(record.text)
        if trade_match:
            source = valid_team(trade_match.group("src"))
            destination = valid_team(trade_match.group("dest"))
            if source and destination and source != destination:
                movement = Movement(
                    player=record.player,
                    source=source,
                    destination=destination,
                    move_type="trade",
                    date=record.date,
                    description=record.text,
                    player_url=record.player_url,
                )
                key = (
                    player_key,
                    source,
                    destination,
                    movement.move_type,
                    movement.date,
                )
                if key not in seen:
                    seen.add(key)
                    movements.append(movement)
            continue

        if is_nonfinal_offer_sheet_record(record.text):
            print(
                f"  {record.player}: ignoring non-final offer-sheet record "
                f"from {record.date}"
            )
            continue

        sign_match = SIGN_DEST_RE.search(record.text)
        claim_match = CLAIM_DEST_RE.search(record.text)
        destination = valid_team(
            sign_match.group("dest") if sign_match else claim_match.group("dest")
            if claim_match
            else None
        )
        if destination is None:
            continue

        prior_departure = latest_departure_before(
            departures.get(player_key, []), record.parsed_date
        )
        source = (
            overrides.get(player_key)
            or (prior_departure.team if prior_departure else None)
            or free_agent_sources.get(player_key)
        )

        # Re-signings and contract changes with the same team are not movements.
        if source == destination:
            continue

        if source is None:
            unresolved.append(
                {
                    "player": record.player,
                    "date": record.date,
                    "destination": destination,
                    "description": record.text,
                    "player_url": canonical_spotrac_player_url(record.player_url),
                    "suggestion": (
                        "Add the player's former team to an overrides JSON file, "
                        'for example: {"Player Name": "LAL"}'
                    ),
                }
            )
            continue

        movement = Movement(
            player=record.player,
            source=source,
            destination=destination,
            move_type="free_agent",
            date=record.date,
            description=record.text,
            player_url=record.player_url,
        )
        key = (
            player_key,
            source,
            destination,
            movement.move_type,
            movement.date,
        )
        if key not in seen:
            seen.add(key)
            movements.append(movement)

    return movements, unresolved


def _order_same_day_movements(
    movements: list[Movement],
    expected_source: str | None,
) -> list[Movement]:
    """Order equal-date movements by team continuity, not input page order."""
    remaining = list(movements)
    ordered: list[Movement] = []
    current_team = expected_source

    while remaining:
        candidate_index: int | None = None

        if current_team:
            candidate_index = next(
                (
                    index
                    for index, movement in enumerate(remaining)
                    if movement.source == current_team
                ),
                None,
            )

        if candidate_index is None:
            destinations = {movement.destination for movement in remaining}
            candidate_index = next(
                (
                    index
                    for index, movement in enumerate(remaining)
                    if movement.source not in destinations
                ),
                0,
            )

        movement = remaining.pop(candidate_index)
        ordered.append(movement)
        current_team = movement.destination

    return ordered


def collapse_player_movements(movements: list[Movement]) -> list[Movement]:
    """Keep at most one edge per player while preserving the real team chain.

    Transaction pages often list equal-date moves newest first. Sorting by date
    alone therefore turns a draft-day chain such as NYK -> HOU -> LAC into
    HOU -> LAC followed by NYK -> HOU, which previously collapsed to HOU -> HOU.
    """
    grouped: dict[str, list[Movement]] = defaultdict(list)
    order: list[str] = []

    for movement in movements:
        player_key = canonical_player_name(movement.player)
        if player_key not in grouped:
            order.append(player_key)
        grouped[player_key].append(movement)

    collapsed: list[Movement] = []
    for player_key in order:
        player_movements = grouped[player_key]

        by_date: dict[datetime, list[Movement]] = defaultdict(list)
        for movement in player_movements:
            by_date[datetime.strptime(movement.date, "%b %d, %Y")].append(movement)

        chronologically_ordered: list[Movement] = []
        current_team: str | None = None
        for movement_date in sorted(by_date):
            same_day = _order_same_day_movements(
                by_date[movement_date],
                expected_source=current_team,
            )
            chronologically_ordered.extend(same_day)
            if same_day:
                current_team = same_day[-1].destination

        first = chronologically_ordered[0]
        last = chronologically_ordered[-1]

        # A same-team result is not a movement between NBA teams.
        if first.source == last.destination:
            print(
                f"  {first.player}: collapsed route returns to {first.source}; "
                "skipping self-edge"
            )
            continue

        if len(chronologically_ordered) == 1:
            collapsed.append(first)
            continue

        description = (
            f"{last.description} "
            f"(collapsed from {len(chronologically_ordered)} transactions)"
        )
        collapsed.append(
            replace(
                last,
                player=first.player,
                source=first.source,
                destination=last.destination,
                move_type=last.move_type,
                date=last.date,
                description=description,
                player_url=last.player_url or first.player_url,
            )
        )

    return collapsed


def movement_graph(movements: Iterable[Movement]) -> nx.MultiDiGraph:
    graph = nx.MultiDiGraph()
    for abbreviation, full_name in NBA_TEAMS.items():
        graph.add_node(
            abbreviation,
            name=full_name,
            logo_url=nba_logo_url(abbreviation),
        )

    for movement in movements:
        graph.add_edge(
            movement.source,
            movement.destination,
            player=movement.player,
            move_type=movement.move_type,
            date=movement.date,
            description=movement.description,
            salary=movement.salary,
            salary_source=movement.salary_source,
            weight=movement.salary or 0,
        )
    return graph



def _pair_key(source: str, destination: str) -> tuple[str, str]:
    return tuple(sorted((source, destination)))


def build_layout_graph(graph: nx.MultiDiGraph) -> nx.Graph:
    """Collapse player edges to team-pair edges for layout optimization.

    Parallel movements are retained as counts and salaries. The spring force uses
    movement count, while the crossing-aware score gives extra importance to
    routes carrying highly paid players.
    """
    layout_graph = nx.Graph()
    layout_graph.add_nodes_from(graph.nodes)
    for source, destination, data in graph.edges(data=True):
        salary = float(data.get("salary") or 0)
        if layout_graph.has_edge(source, destination):
            edge = layout_graph[source][destination]
            edge["count"] += 1
            edge["total_salary"] += salary
            edge["max_salary"] = max(edge["max_salary"], salary)
        else:
            layout_graph.add_edge(
                source,
                destination,
                count=1,
                total_salary=salary,
                max_salary=salary,
            )

    for _source, _destination, data in layout_graph.edges(data=True):
        # More transactions create a stronger attraction, but logarithmic
        # scaling avoids collapsing busy teams into the center.
        data["weight"] = 1.0 + math.log1p(data["count"])
        data["importance"] = (
            1.0
            + 0.45 * math.log1p(data["count"])
            + 0.35 * math.log1p(data["total_salary"] / 1_000_000)
        )
    return layout_graph


def normalize_positions(
    positions: dict[str, tuple[float, float]],
    target_span: float = 2.0,
) -> dict[str, tuple[float, float]]:
    """Center a layout and give all candidates a comparable scale."""
    if not positions:
        return {}
    xs = [coords[0] for coords in positions.values()]
    ys = [coords[1] for coords in positions.values()]
    center_x = (min(xs) + max(xs)) / 2
    center_y = (min(ys) + max(ys)) / 2
    span = max(max(xs) - min(xs), max(ys) - min(ys), 1e-9)
    scale = target_span / span
    return {
        node: ((coords[0] - center_x) * scale, (coords[1] - center_y) * scale)
        for node, coords in positions.items()
    }


def enforce_minimum_node_separation(
    positions: dict[str, tuple[float, float]],
    minimum_distance: float = 0.22,
    iterations: int = 300,
) -> dict[str, tuple[float, float]]:
    """Move overlapping logos apart while preserving the layout."""
    nodes = list(positions)
    mutable = {node: [positions[node][0], positions[node][1]] for node in nodes}

    for _ in range(iterations):
        changed = False
        for i, first in enumerate(nodes):
            for j in range(i + 1, len(nodes)):
                second = nodes[j]
                dx = mutable[second][0] - mutable[first][0]
                dy = mutable[second][1] - mutable[first][1]
                distance = math.hypot(dx, dy)
                if distance >= minimum_distance:
                    continue

                if distance < 1e-9:
                    angle = math.radians((i * 37 + j * 71) % 360)
                    dx, dy = math.cos(angle), math.sin(angle)
                    distance = 1.0

                shift = (minimum_distance - distance) / 2
                ux, uy = dx / distance, dy / distance
                mutable[first][0] -= ux * shift
                mutable[first][1] -= uy * shift
                mutable[second][0] += ux * shift
                mutable[second][1] += uy * shift
                changed = True
        if not changed:
            break

    return normalize_positions(
        {node: (coords[0], coords[1]) for node, coords in mutable.items()}
    )


def _orientation(
    first: tuple[float, float],
    second: tuple[float, float],
    third: tuple[float, float],
) -> float:
    return (
        (second[0] - first[0]) * (third[1] - first[1])
        - (second[1] - first[1]) * (third[0] - first[0])
    )


def segments_cross(
    a1: tuple[float, float],
    a2: tuple[float, float],
    b1: tuple[float, float],
    b2: tuple[float, float],
    epsilon: float = 1e-10,
) -> bool:
    """Return True for a proper line-segment crossing, excluding touching."""
    o1 = _orientation(a1, a2, b1)
    o2 = _orientation(a1, a2, b2)
    o3 = _orientation(b1, b2, a1)
    o4 = _orientation(b1, b2, a2)
    return (
        ((o1 > epsilon and o2 < -epsilon) or (o1 < -epsilon and o2 > epsilon))
        and ((o3 > epsilon and o4 < -epsilon) or (o3 < -epsilon and o4 > epsilon))
    )


def point_to_segment_distance(
    point: tuple[float, float],
    start: tuple[float, float],
    end: tuple[float, float],
) -> float:
    dx = end[0] - start[0]
    dy = end[1] - start[1]
    squared_length = dx * dx + dy * dy
    if squared_length <= 1e-12:
        return math.dist(point, start)
    projection = (
        (point[0] - start[0]) * dx + (point[1] - start[1]) * dy
    ) / squared_length
    projection = min(1.0, max(0.0, projection))
    closest = (start[0] + projection * dx, start[1] + projection * dy)
    return math.dist(point, closest)


def layout_visibility_score(
    graph: nx.Graph,
    positions: dict[str, tuple[float, float]],
    node_clearance: float = 0.16,
    minimum_angle_degrees: float = 24.0,
) -> tuple[float, dict[str, float]]:
    """Score a layout by how clearly its routes can be followed.

    Edge crossings are the largest penalty. The score also penalizes edges that
    pass through unrelated team logos and incident edges that leave a team at
    nearly the same angle. A modest length term keeps the result compact without
    recreating the dense central knot caused by minimizing length alone.
    """
    edges = list(graph.edges(data=True))
    total_importance = sum(data.get("importance", 1.0) for *_uv, data in edges) or 1.0

    weighted_length = sum(
        data.get("importance", 1.0) * math.dist(positions[source], positions[destination])
        for source, destination, data in edges
    ) / total_importance

    crossing_penalty = 0.0
    crossing_count = 0
    for first_index, (a, b, first_data) in enumerate(edges):
        for c, d, second_data in edges[first_index + 1 :]:
            if len({a, b, c, d}) < 4:
                continue
            if segments_cross(positions[a], positions[b], positions[c], positions[d]):
                crossing_count += 1
                crossing_penalty += (
                    first_data.get("importance", 1.0)
                    + second_data.get("importance", 1.0)
                ) / 2

    node_edge_penalty = 0.0
    node_edge_conflicts = 0
    for source, destination, data in edges:
        importance = data.get("importance", 1.0)
        for node in graph.nodes:
            if node in {source, destination}:
                continue
            distance = point_to_segment_distance(
                positions[node], positions[source], positions[destination]
            )
            if distance < node_clearance:
                node_edge_conflicts += 1
                node_edge_penalty += importance * (
                    (node_clearance - distance) / node_clearance
                ) ** 2

    angle_penalty = 0.0
    narrow_angle_count = 0
    for node in graph.nodes:
        neighbors = list(graph.neighbors(node))
        for first_index, first in enumerate(neighbors):
            vector_a = (
                positions[first][0] - positions[node][0],
                positions[first][1] - positions[node][1],
            )
            length_a = math.hypot(*vector_a)
            for second in neighbors[first_index + 1 :]:
                vector_b = (
                    positions[second][0] - positions[node][0],
                    positions[second][1] - positions[node][1],
                )
                length_b = math.hypot(*vector_b)
                if length_a <= 1e-9 or length_b <= 1e-9:
                    continue
                cosine = (
                    vector_a[0] * vector_b[0] + vector_a[1] * vector_b[1]
                ) / (length_a * length_b)
                angle = math.degrees(math.acos(max(-1.0, min(1.0, cosine))))
                if angle < minimum_angle_degrees:
                    narrow_angle_count += 1
                    angle_penalty += (
                        (minimum_angle_degrees - angle) / minimum_angle_degrees
                    ) ** 2

    # Crossing and logo-collision penalties dominate the modest compactness term.
    score = (
        1.8 * weighted_length
        + 18.0 * crossing_penalty
        + 11.0 * node_edge_penalty
        + 3.5 * angle_penalty
    )
    metrics = {
        "weighted_length": weighted_length,
        "crossings": float(crossing_count),
        "node_edge_conflicts": float(node_edge_conflicts),
        "narrow_angles": float(narrow_angle_count),
        "score": score,
    }
    return score, metrics


def refine_layout_for_visibility(
    graph: nx.Graph,
    initial_positions: dict[str, tuple[float, float]],
    steps: int = 1200,
    seed: int = 0,
) -> tuple[dict[str, tuple[float, float]], dict[str, float]]:
    """Use a small simulated-annealing pass to remove crossings and collisions."""
    if len(graph) <= 2 or steps <= 0:
        score, metrics = layout_visibility_score(graph, initial_positions)
        return initial_positions, metrics

    rng = random.Random(seed)
    positions = dict(initial_positions)
    current_score, current_metrics = layout_visibility_score(graph, positions)
    best_positions = dict(positions)
    best_score = current_score
    best_metrics = current_metrics
    nodes = list(graph.nodes)

    for step in range(steps):
        progress = step / max(steps - 1, 1)
        temperature = 0.14 * (1.0 - progress) + 0.012
        node = rng.choice(nodes)
        old_position = positions[node]
        angle = rng.random() * 2 * math.pi
        radius = temperature * (0.35 + 0.65 * rng.random())
        proposed = (
            max(-1.35, min(1.35, old_position[0] + math.cos(angle) * radius)),
            max(-1.35, min(1.35, old_position[1] + math.sin(angle) * radius)),
        )

        if any(
            other != node and math.dist(proposed, positions[other]) < 0.18
            for other in nodes
        ):
            continue

        positions[node] = proposed
        candidate_score, candidate_metrics = layout_visibility_score(graph, positions)
        delta = candidate_score - current_score
        accept = delta <= 0 or rng.random() < math.exp(
            -delta / max(temperature * 8.0, 1e-9)
        )
        if accept:
            current_score = candidate_score
            current_metrics = candidate_metrics
            if candidate_score < best_score:
                best_score = candidate_score
                best_positions = dict(positions)
                best_metrics = candidate_metrics
        else:
            positions[node] = old_position

    return normalize_positions(best_positions), best_metrics


def compute_component_layout(
    component_graph: nx.Graph,
    restarts: int,
    refinement_steps: int,
    seed_offset: int,
) -> tuple[dict[str, tuple[float, float]], dict[str, float]]:
    nodes = list(component_graph.nodes)
    if len(nodes) == 1:
        positions = {nodes[0]: (0.0, 0.0)}
        return positions, {
            "weighted_length": 0.0,
            "crossings": 0.0,
            "node_edge_conflicts": 0.0,
            "narrow_angles": 0.0,
            "score": 0.0,
        }
    if len(nodes) == 2:
        positions = {nodes[0]: (-0.5, 0.0), nodes[1]: (0.5, 0.0)}
        score, metrics = layout_visibility_score(component_graph, positions)
        return positions, metrics

    candidates: list[tuple[float, dict[str, tuple[float, float]], dict[str, float]]] = []
    k_values = (0.34, 0.44, 0.56, 0.70)
    for run in range(max(1, restarts)):
        seed = seed_offset + run
        initial = nx.circular_layout(component_graph) if run % 7 == 0 else None
        raw = nx.spring_layout(
            component_graph,
            seed=seed,
            pos=initial,
            k=k_values[run % len(k_values)],
            iterations=1300,
            threshold=1e-5,
            weight="weight",
            scale=1.0,
        )
        normalized = normalize_positions(
            {node: (float(coords[0]), float(coords[1])) for node, coords in raw.items()}
        )
        separated = enforce_minimum_node_separation(normalized)
        score, metrics = layout_visibility_score(component_graph, separated)
        candidates.append((score, separated, metrics))

    # Kamada-Kawai often supplies a useful candidate with different crossings.
    try:
        raw_kk = nx.kamada_kawai_layout(component_graph, weight="weight", scale=1.0)
        kk_positions = enforce_minimum_node_separation(
            normalize_positions(
                {node: (float(coords[0]), float(coords[1])) for node, coords in raw_kk.items()}
            )
        )
        kk_score, kk_metrics = layout_visibility_score(component_graph, kk_positions)
        candidates.append((kk_score, kk_positions, kk_metrics))
    except Exception:
        pass

    candidates.sort(key=lambda item: item[0])
    best_score, best_positions, best_metrics = candidates[0]

    # Refine the strongest few candidates rather than trusting edge length alone.
    for candidate_index, (_score, candidate_positions, _metrics) in enumerate(candidates[:3]):
        refined, refined_metrics = refine_layout_for_visibility(
            component_graph,
            candidate_positions,
            steps=refinement_steps,
            seed=seed_offset + 10_000 + candidate_index,
        )
        refined_score = refined_metrics["score"]
        if refined_score < best_score:
            best_score = refined_score
            best_positions = refined
            best_metrics = refined_metrics

    return best_positions, best_metrics


def _component_bbox(
    positions: dict[str, tuple[float, float]],
) -> tuple[float, float, float, float]:
    xs = [coords[0] for coords in positions.values()]
    ys = [coords[1] for coords in positions.values()]
    return min(xs), max(xs), min(ys), max(ys)


def pack_component_layouts(
    component_layouts: list[tuple[list[str], dict[str, tuple[float, float]]]],
    gap: float = 0.34,
) -> dict[str, tuple[float, float]]:
    """Pack disconnected components beneath the largest component.

    Disconnected components have no meaningful force relationship. Packing them
    explicitly avoids the large empty regions produced by a global spring layout.
    """
    component_layouts = sorted(component_layouts, key=lambda item: len(item[0]), reverse=True)
    largest_size = max(len(nodes) for nodes, _positions in component_layouts)
    packed: dict[str, tuple[float, float]] = {}

    main_nodes, main_positions = component_layouts[0]
    packed.update(main_positions)
    main_min_x, main_max_x, main_min_y, _main_max_y = _component_bbox(main_positions)
    target_row_width = max(main_max_x - main_min_x, 2.0)

    cursor_x = main_min_x
    cursor_y = main_min_y - gap
    row_height = 0.0

    for nodes, local_positions in component_layouts[1:]:
        size_ratio = math.sqrt(len(nodes) / largest_size)
        factor = min(0.72, max(0.34, size_ratio))
        scaled = {
            node: (coords[0] * factor, coords[1] * factor)
            for node, coords in local_positions.items()
        }
        min_x, max_x, min_y, max_y = _component_bbox(scaled)
        width = max(max_x - min_x, 0.34)
        height = max(max_y - min_y, 0.34)

        if cursor_x > main_min_x and cursor_x + width > main_min_x + target_row_width:
            cursor_x = main_min_x
            cursor_y -= row_height + gap
            row_height = 0.0

        offset_x = cursor_x - min_x
        offset_y = cursor_y - max_y
        for node, (x, y) in scaled.items():
            packed[node] = (x + offset_x, y + offset_y)

        cursor_x += width + gap
        row_height = max(row_height, height)

    xs = [coords[0] for coords in packed.values()]
    ys = [coords[1] for coords in packed.values()]
    center_x = (min(xs) + max(xs)) / 2
    center_y = (min(ys) + max(ys)) / 2
    return {
        node: (coords[0] - center_x, coords[1] - center_y)
        for node, coords in packed.items()
    }


def compute_team_layout(
    graph: nx.MultiDiGraph,
    restarts: int = 24,
    refinement_steps: int = 1200,
) -> dict[str, tuple[float, float]]:
    """Compute a component-aware, crossing-aware layout.

    Minimizing only total edge length pulls busy teams into one dense knot. This
    version evaluates edge crossings, routes through logos, and poor angular
    separation, then packs disconnected components into a compact canvas.
    """
    layout_graph = build_layout_graph(graph)
    components = sorted(nx.connected_components(layout_graph), key=len, reverse=True)
    component_layouts: list[tuple[list[str], dict[str, tuple[float, float]]]] = []
    total_metrics = defaultdict(float)

    for component_index, component_nodes in enumerate(components):
        component_graph = layout_graph.subgraph(component_nodes).copy()
        positions, metrics = compute_component_layout(
            component_graph,
            restarts=max(1, restarts),
            refinement_steps=max(0, refinement_steps),
            seed_offset=component_index * 1000,
        )
        component_layouts.append((sorted(component_nodes), positions))
        for name, value in metrics.items():
            total_metrics[name] += value

    packed = pack_component_layouts(component_layouts)
    print(
        "Selected crossing-aware component layout; "
        f"crossings={int(total_metrics['crossings'])}; "
        f"logo/edge conflicts={int(total_metrics['node_edge_conflicts'])}; "
        f"narrow angles={int(total_metrics['narrow_angles'])}; "
        f"components={len(components)}"
    )
    return packed


def edge_visual_widths(
    graph: nx.MultiDiGraph,
    minimum: float = 0.7,
    maximum: float = 7.5,
) -> dict[tuple[str, str, int], float]:
    """Scale widths by salary using a square-root transform."""
    salaries = [
        int(data["salary"])
        for *_edge, data in graph.edges(keys=True, data=True)
        if data.get("salary")
    ]
    maximum_salary = max(salaries, default=1)
    widths: dict[tuple[str, str, int], float] = {}
    for source, destination, key, data in graph.edges(keys=True, data=True):
        salary = int(data.get("salary") or 0)
        ratio = math.sqrt(salary / maximum_salary) if salary > 0 else 0.0
        widths[(source, destination, key)] = minimum + (maximum - minimum) * ratio
    return widths


def edge_visual_alphas(
    graph: nx.MultiDiGraph,
    minimum: float = 0.18,
    maximum: float = 0.88,
) -> dict[tuple[str, str, int], float]:
    """Make lower-salary edges quieter and high-salary routes prominent."""
    salaries = [
        int(data["salary"])
        for *_edge, data in graph.edges(keys=True, data=True)
        if data.get("salary")
    ]
    maximum_salary = max(salaries, default=1)
    alphas: dict[tuple[str, str, int], float] = {}
    for source, destination, key, data in graph.edges(keys=True, data=True):
        salary = int(data.get("salary") or 0)
        ratio = math.sqrt(salary / maximum_salary) if salary > 0 else 0.0
        alphas[(source, destination, key)] = minimum + (maximum - minimum) * ratio
    return alphas


def edge_curvatures(
    graph: nx.MultiDiGraph,
    spacing: float = 0.105,
) -> dict[tuple[str, str, int], float]:
    """Assign separate curves to parallel and opposite-direction movements."""
    unordered_groups: dict[
        tuple[str, str], list[tuple[str, str, int, dict]]
    ] = defaultdict(list)
    for source, destination, key, data in graph.edges(keys=True, data=True):
        unordered_groups[_pair_key(source, destination)].append(
            (source, destination, key, data)
        )

    result: dict[tuple[str, str, int], float] = {}
    for (left, right), edges in unordered_groups.items():
        by_direction: dict[tuple[str, str], list[tuple[str, str, int, dict]]] = defaultdict(list)
        for edge in edges:
            by_direction[(edge[0], edge[1])].append(edge)

        if len(by_direction) == 1:
            direction_edges = next(iter(by_direction.values()))
            direction_edges.sort(key=lambda edge: int(edge[3].get("salary") or 0), reverse=True)
            center = (len(direction_edges) - 1) / 2
            for index, (source, destination, key, _data) in enumerate(direction_edges):
                result[(source, destination, key)] = (index - center) * spacing
        else:
            # The same positive curvature bends reverse-direction edges onto the
            # opposite geometric side, keeping arrows and labels distinguishable.
            for direction_edges in by_direction.values():
                direction_edges.sort(
                    key=lambda edge: int(edge[3].get("salary") or 0), reverse=True
                )
                for index, (source, destination, key, _data) in enumerate(direction_edges):
                    result[(source, destination, key)] = 0.08 + index * spacing

    return result


def interactive_edge_lanes(
    graph: nx.MultiDiGraph,
) -> dict[tuple[str, str, int], float]:
    """Assign a geometric lane to each interactive edge.

    Curvature alone does not separate parallel edges near the team logos because
    all curves still share the same source and destination anchor points.  Lane
    values are therefore used to shift the transparent endpoint anchors sideways.

    For one-way traffic, lanes are centred around zero.  When transactions run in
    both directions, each direction is placed on a different geometric side of
    the team pair: a positive lane is enough because the local perpendicular
    vector reverses when source and destination are reversed.
    """
    unordered_groups: dict[
        tuple[str, str], list[tuple[str, str, int, dict]]
    ] = defaultdict(list)
    for source, destination, key, data in graph.edges(keys=True, data=True):
        unordered_groups[_pair_key(source, destination)].append(
            (source, destination, key, data)
        )

    lanes: dict[tuple[str, str, int], float] = {}
    for edges in unordered_groups.values():
        by_direction: dict[
            tuple[str, str], list[tuple[str, str, int, dict]]
        ] = defaultdict(list)
        for edge in edges:
            by_direction[(edge[0], edge[1])].append(edge)

        if len(by_direction) == 1:
            direction_edges = next(iter(by_direction.values()))
            direction_edges.sort(
                key=lambda edge: int(edge[3].get("salary") or 0),
                reverse=True,
            )
            centre = (len(direction_edges) - 1) / 2.0
            for index, (source, destination, key, _data) in enumerate(direction_edges):
                lanes[(source, destination, key)] = index - centre
        else:
            for direction_edges in by_direction.values():
                direction_edges.sort(
                    key=lambda edge: int(edge[3].get("salary") or 0),
                    reverse=True,
                )
                for index, (source, destination, key, _data) in enumerate(direction_edges):
                    # Half-integer lanes leave an empty centre corridor and keep
                    # the two directions clearly separated.
                    lanes[(source, destination, key)] = index + 0.5

    return lanes


def selected_edge_labels(
    graph: nx.MultiDiGraph,
    maximum_labels: int,
) -> set[tuple[str, str, int]]:
    """Choose the highest-salary movements for permanent labels."""
    if maximum_labels <= 0:
        return set()
    ranked = sorted(
        graph.edges(keys=True, data=True),
        key=lambda edge: int(edge[3].get("salary") or 0),
        reverse=True,
    )
    return {(source, destination, key) for source, destination, key, _data in ranked[:maximum_labels]}

def download_team_logo(team: str, logo_cache_dir: Path) -> Path:
    """Download and convert an official NBA SVG logo to a local PNG."""
    logo_cache_dir.mkdir(parents=True, exist_ok=True)
    png_path = logo_cache_dir / f"{team}.png"
    if png_path.exists():
        return png_path

    request = urllib.request.Request(
        nba_logo_url(team),
        headers={"User-Agent": "Mozilla/5.0"},
    )
    with urllib.request.urlopen(request, timeout=30) as response:
        svg_bytes = response.read()
    cairosvg.svg2png(
        bytestring=svg_bytes,
        write_to=str(png_path),
        output_width=300,
        output_height=300,
    )
    return png_path


def load_team_logos(logo_cache_dir: Path) -> dict[str, Image.Image]:
    logos: dict[str, Image.Image] = {}
    for team in NBA_TEAMS:
        try:
            path = download_team_logo(team, logo_cache_dir)
            with Image.open(path) as image:
                logos[team] = image.convert("RGBA").copy()
        except Exception as error:
            print(f"Warning: could not load {team} logo: {error}")
    return logos



def draw_static_graph(
    graph: nx.MultiDiGraph,
    positions: dict[str, tuple[float, float]],
    output_path: Path,
    logo_cache_dir: Path,
    maximum_labels: int = 12,
    team_label_offset_points: float = -22.0,
) -> None:
    """Create a static PNG with salary-prioritized routes and labels."""
    output_path.parent.mkdir(parents=True, exist_ok=True)
    figure, axis = plt.subplots(figsize=(22, 18))
    axis.set_axis_off()
    edge_widths = edge_visual_widths(graph)
    edge_alphas = edge_visual_alphas(graph)
    curvatures = edge_curvatures(graph)
    labelled_edges = selected_edge_labels(graph, maximum_labels)

    # A smaller backing than the previous version leaves more room for routes.
    nx.draw_networkx_nodes(
        graph,
        positions,
        node_size=1850,
        node_color="white",
        linewidths=0.7,
        edgecolors="#c8c8c8",
        ax=axis,
    )

    # Draw low-salary edges first. High-salary movements are rendered last and
    # therefore stay visible at intersections.
    edges = sorted(
        graph.edges(keys=True, data=True),
        key=lambda edge: int(edge[3].get("salary") or 0),
    )
    for source, destination, key, data in edges:
        curvature = curvatures[(source, destination, key)]
        style = "solid" if data["move_type"] == "trade" else "dashed"
        color = "#1f5f99" if data["move_type"] == "trade" else "#4f5963"
        salary = int(data.get("salary") or 0)
        width = edge_widths[(source, destination, key)]
        alpha = edge_alphas[(source, destination, key)]
        nx.draw_networkx_edges(
            graph,
            positions,
            edgelist=[(source, destination)],
            width=width,
            style=style,
            edge_color=color,
            alpha=alpha,
            arrows=True,
            arrowsize=10 + 1.2 * width,
            min_source_margin=26,
            min_target_margin=26,
            connectionstyle=f"arc3,rad={curvature}",
            ax=axis,
        )

        if (source, destination, key) not in labelled_edges:
            continue

        # Label placement follows the approximate midpoint of the curved route.
        x1, y1 = positions[source]
        x2, y2 = positions[destination]
        midpoint_x = (x1 + x2) / 2
        midpoint_y = (y1 + y2) / 2
        dx, dy = x2 - x1, y2 - y1
        length = math.hypot(dx, dy) or 1.0
        offset = curvature * 0.42
        label_x = midpoint_x - dy / length * offset
        label_y = midpoint_y + dx / length * offset
        axis.text(
            label_x,
            label_y,
            f"{data['player']}\n{format_salary(salary or None)}",
            fontsize=6.3,
            fontweight="bold" if salary else "normal",
            ha="center",
            va="center",
            zorder=20,
            bbox={
                "boxstyle": "round,pad=0.13",
                "fc": "white",
                "ec": "none",
                "alpha": 0.88,
            },
        )

    logos = load_team_logos(logo_cache_dir)
    for team, (x, y) in positions.items():
        if team in logos:
            image_box = OffsetImage(logos[team], zoom=0.135)
            axis.add_artist(
                AnnotationBbox(
                    image_box,
                    (x, y),
                    frameon=False,
                    box_alignment=(0.5, 0.5),
                    zorder=30,
                )
            )
        else:
            axis.text(
                x,
                y,
                team,
                fontsize=10,
                fontweight="bold",
                ha="center",
                va="center",
                zorder=30,
            )
        axis.annotate(
            team,
            (x, y),
            xytext=(0, team_label_offset_points),
            textcoords="offset points",
            ha="center",
            va="top",
            fontsize=7.5,
            zorder=31,
        )

    legend = [
        Line2D([0], [0], color="#1f5f99", linestyle="solid", label="Trade"),
        Line2D(
            [0],
            [0],
            color="#4f5963",
            linestyle="dashed",
            label="Free agent / waiver signing",
        ),
        Line2D(
            [0],
            [0],
            color="#555555",
            linewidth=5,
            alpha=0.85,
            label="Higher salary = wider / darker",
        ),
    ]
    axis.legend(handles=legend, loc="upper left", fontsize=10, frameon=False)
    label_note = (
        f"Top {maximum_labels} salaries are labelled; all players appear on hover in HTML"
        if maximum_labels > 0
        else "Player names are available on hover in the interactive HTML"
    )
    axis.set_title(
        f"NBA Player Movements, {START_DATE} to {END_DATE}\n"
        f"Crossing-aware layout; {label_note}",
        fontsize=17,
        pad=22,
    )
    axis.margins(0.10)
    figure.tight_layout()
    figure.savefig(output_path, dpi=230, bbox_inches="tight")
    plt.close(figure)


def _rgba(hex_color: str, alpha: float) -> str:
    red = int(hex_color[1:3], 16)
    green = int(hex_color[3:5], 16)
    blue = int(hex_color[5:7], 16)
    return f"rgba({red},{green},{blue},{alpha:.3f})"



def _interactive_edge_anchor_positions(
    source_position: tuple[float, float],
    destination_position: tuple[float, float],
    node_radius: float,
    extra_gap: float,
    lateral_offset: float = 0.0,
) -> tuple[tuple[float, float], tuple[float, float]]:
    """Return edge endpoints outside the logos and in a parallel lane.

    The longitudinal offset keeps the line out of transparent logo interiors.
    The lateral offset shifts both endpoint anchors along the perpendicular to
    the source-to-destination direction.  This means parallel player edges no
    longer converge on exactly the same two points near the team logos.
    """
    source_x, source_y = source_position
    destination_x, destination_y = destination_position
    delta_x = destination_x - source_x
    delta_y = destination_y - source_y
    distance = math.hypot(delta_x, delta_y)
    if distance <= 1e-9:
        return source_position, destination_position

    unit_x = delta_x / distance
    unit_y = delta_y / distance
    perpendicular_x = -unit_y
    perpendicular_y = unit_x

    requested_offset = max(0.0, node_radius + extra_gap)
    # Prevent the two anchors from passing each other for unusually close nodes.
    maximum_offset = max(0.0, distance / 2.0 - 2.0)
    longitudinal_offset = min(requested_offset, maximum_offset)

    sideways_x = perpendicular_x * lateral_offset
    sideways_y = perpendicular_y * lateral_offset

    return (
        (
            source_x + unit_x * longitudinal_offset + sideways_x,
            source_y + unit_y * longitudinal_offset + sideways_y,
        ),
        (
            destination_x - unit_x * longitudinal_offset + sideways_x,
            destination_y - unit_y * longitudinal_offset + sideways_y,
        ),
    )


def draw_interactive_graph(
    graph: nx.MultiDiGraph,
    positions: dict[str, tuple[float, float]],
    output_path: Path,
    maximum_labels: int = 0,
    node_size: int = 31,
    endpoint_gap: float = 8.0,
    parallel_edge_spacing: float = 13.0,
    hover_target_width: float = 10.0,
    team_label_vadjust: float = -8.0,
) -> None:
    """Create an interactive graph whose visible edges stop outside both logos.

    Team logos are transparent SVG images.  Vis-network normally draws an edge
    from the source node centre and then paints the image over it; transparent
    parts of the logo allow that centre-to-boundary segment to remain visible.
    ``endPointOffset`` does not consistently solve this for image nodes.

    Each visible player edge is therefore drawn between two tiny transparent
    anchor nodes.  One anchor is placed just beyond the source logo and one just
    before the destination logo.  This makes incoming and outgoing edges behave
    symmetrically and avoids lines appearing to originate at a logo's centre.
    """
    output_path.parent.mkdir(parents=True, exist_ok=True)
    network = Network(
        height="100%",
        width="100%",
        directed=True,
        bgcolor="#ffffff",
        font_color="#111111",
        notebook=False,
    )

    canvas_scale = 700
    canvas_positions: dict[str, tuple[float, float]] = {}
    for abbreviation in NBA_TEAMS:
        x, y = positions[abbreviation]
        canvas_position = (canvas_scale * x, -canvas_scale * y)
        canvas_positions[abbreviation] = canvas_position
        network.add_node(
            abbreviation,
            label=abbreviation,
            title=NBA_TEAMS[abbreviation],
            x=canvas_position[0],
            y=canvas_position[1],
            fixed={"x": True, "y": True},
            physics=False,
            shape="image",
            image=nba_logo_url(abbreviation),
            size=node_size,
            borderWidth=0,
            # Negative values move an image node's label upward, closer to its logo.
            font={"vadjust": float(team_label_vadjust)},
        )

    edge_widths = edge_visual_widths(graph)
    edge_alphas = edge_visual_alphas(graph)
    lanes = interactive_edge_lanes(graph)
    labelled_edges = selected_edge_labels(graph, maximum_labels)

    edges = sorted(
        graph.edges(keys=True, data=True),
        key=lambda edge: int(edge[3].get("salary") or 0),
    )
    for edge_number, (source, destination, key, data) in enumerate(edges):
        edge_id = (source, destination, key)
        lane = lanes[edge_id]
        base_color = "#1f5f99" if data["move_type"] == "trade" else "#4f5963"

        source_anchor_position, destination_anchor_position = (
            _interactive_edge_anchor_positions(
                canvas_positions[source],
                canvas_positions[destination],
                node_radius=float(node_size),
                extra_gap=float(endpoint_gap),
                lateral_offset=lane * max(0.0, float(parallel_edge_spacing)),
            )
        )
        source_anchor = f"__edge_{edge_number}_from"
        destination_anchor = f"__edge_{edge_number}_to"

        # These nodes are effectively invisible but remain valid geometric edge
        # endpoints.  Do not use hidden=True: vis-network hides incident edges
        # when an endpoint node itself is hidden.
        transparent_node = {
            # PyVis treats an empty string as a missing label and may replace it
            # with the node ID.  A zero-width space is non-empty to PyVis but
            # renders as no visible text in vis-network.
            "label": "\u200b",
            "title": "",
            "font": {
                "size": 0,
                "color": "rgba(0,0,0,0)",
                "strokeWidth": 0,
            },
            "shape": "dot",
            "size": 0.1,
            "borderWidth": 0,
            "color": {
                "background": "rgba(0,0,0,0)",
                "border": "rgba(0,0,0,0)",
                "highlight": {
                    "background": "rgba(0,0,0,0)",
                    "border": "rgba(0,0,0,0)",
                },
                "hover": {
                    "background": "rgba(0,0,0,0)",
                    "border": "rgba(0,0,0,0)",
                },
            },
            "fixed": {"x": True, "y": True},
            "physics": False,
            "chosen": False,
        }
        network.add_node(
            source_anchor,
            x=source_anchor_position[0],
            y=source_anchor_position[1],
            **transparent_node,
        )
        network.add_node(
            destination_anchor,
            x=destination_anchor_position[0],
            y=destination_anchor_position[1],
            **transparent_node,
        )

        tooltip = f"{data['player']} ({format_salary(data.get('salary'))})"

        # The endpoint anchors are already shifted into distinct parallel lanes.
        # Applying vis-network's curvedCW/curvedCCW smoothing on top of that
        # lateral shift can create hooks or U-shaped curves near the teams.
        # Draw the lane as a straight segment instead: the shifted anchors provide
        # the separation, while the visible and invisible hover edges remain
        # geometrically identical.
        smooth_options = {"enabled": False}

        # A nearly transparent, wider edge acts as a mouse target.  This does
        # not alter the salary-dependent visible width, but makes thin player
        # edges much easier to hover once they have been fanned into lanes.
        network.add_edge(
            source_anchor,
            destination_anchor,
            label="",
            title=tooltip,
            dashes=False,
            arrows={"to": {"enabled": False}},
            arrowStrikethrough=False,
            smooth=smooth_options,
            width=max(float(hover_target_width), edge_widths[edge_id] + 4.0),
            color={
                "color": "rgba(0,0,0,0.001)",
                "hover": _rgba(base_color, 0.14),
                "highlight": "rgba(0,0,0,0.001)",
                "inherit": False,
            },
            hoverWidth=0.0,
            selectionWidth=0.0,
            chosen=False,
        )

        network.add_edge(
            source_anchor,
            destination_anchor,
            label=data["player"] if edge_id in labelled_edges else "",
            title=tooltip,
            dashes=data["move_type"] != "trade",
            arrows={
                "to": {
                    "enabled": True,
                    "scaleFactor": 1.0,
                }
            },
            arrowStrikethrough=False,
            smooth=smooth_options,
            width=edge_widths[edge_id],
            color={
                "color": _rgba(base_color, edge_alphas[edge_id]),
                "hover": base_color,
                "highlight": base_color,
                "inherit": False,
            },
            hoverWidth=2.5,
            selectionWidth=3.0,
        )

    network.set_options(
        """
        {
          "physics": {"enabled": false},
          "interaction": {
            "hover": true,
            "navigationButtons": true,
            "tooltipDelay": 80,
            "multiselect": true
          },
          "edges": {
            "font": {
              "size": 10,
              "align": "middle",
              "background": "rgba(255,255,255,0.88)"
            },
            "arrowStrikethrough": false,
            "chosen": true
          },
          "nodes": {
            "font": {"size": 14, "face": "Arial", "vadjust": 8},
            "shapeProperties": {"useBorderWithImage": false}
          }
        }
        """
    )
    network.write_html(str(output_path), open_browser=False)

    html = output_path.read_text(encoding="utf-8")

    html = html.replace(
        "</head>",
        """
        <style>
            html,
            body {
                width: 100%;
                height: 100%;
                margin: 0;
                padding: 0;
                overflow: hidden;
            }

            body {
                display: block;
            }

            .card {
                width: 100% !important;
                height: 100vh !important;
                margin: 0 !important;
                padding: 0 !important;
                border: none !important;
            }

            .card-body {
                width: 100% !important;
                height: 100% !important;
                min-height: 0 !important;
                margin: 0 !important;
                padding: 0 !important;
            }

            #mynetwork {
                width: 100% !important;
                height: 100% !important;
                min-height: 0 !important;
                margin: 0 !important;
                padding: 0 !important;
                border: none !important;
            }

            #graph-legend {
                position: fixed;
                top: 16px;
                left: 16px;
                z-index: 1000;
                min-width: 230px;
                padding: 12px 14px;
                background: rgba(255, 255, 255, 0.94);
                border: 1px solid rgba(0, 0, 0, 0.16);
                border-radius: 8px;
                box-shadow: 0 2px 10px rgba(0, 0, 0, 0.14);
                color: #222;
                font-family: Arial, sans-serif;
                font-size: 13px;
                line-height: 1.35;
                pointer-events: none;
                user-select: none;
            }

            #graph-legend .legend-title {
                margin-bottom: 8px;
                font-size: 14px;
                font-weight: 700;
            }

            #graph-legend .legend-row {
                display: flex;
                align-items: center;
                gap: 10px;
                margin: 6px 0;
                white-space: nowrap;
            }

            #graph-legend .legend-line {
                display: inline-block;
                width: 54px;
                flex: 0 0 54px;
                border-top-color: #1f5f99;
                border-top-style: solid;
            }

            #graph-legend .legend-trade {
                border-top-width: 4px;
            }

            #graph-legend .legend-free-agent {
                border-top-width: 4px;
                border-top-style: dashed;
                border-top-color: #4f5963;
            }

            #graph-legend .legend-thin {
                border-top-width: 1px;
                border-top-color: #1f5f99;
            }

            #graph-legend .legend-thick {
                border-top-width: 8px;
                border-top-color: #1f5f99;
            }

            #graph-legend .legend-note {
                margin-top: 8px;
                color: #555;
                font-size: 12px;
                white-space: normal;
            }

            @media (max-width: 700px) {
                #graph-legend {
                    top: 8px;
                    left: 8px;
                    min-width: 0;
                    padding: 9px 10px;
                    font-size: 11px;
                }

                #graph-legend .legend-title {
                    font-size: 12px;
                }

                #graph-legend .legend-line {
                    width: 40px;
                    flex-basis: 40px;
                }
            }
        </style>
        </head>
        """,
    )

    html = html.replace(
        "</body>",
        """
        <div id="graph-legend" aria-label="Graph legend">
            <div class="legend-title">NBA player movements</div>
            <div class="legend-row">
                <span class="legend-line legend-trade"></span>
                <span>Trade</span>
            </div>
            <div class="legend-row">
                <span class="legend-line legend-free-agent"></span>
                <span>Free-agent signing</span>
            </div>
            <div class="legend-row">
                <span class="legend-line legend-thin"></span>
                <span>Lower salary</span>
            </div>
            <div class="legend-row">
                <span class="legend-line legend-thick"></span>
                <span>Higher salary</span>
            </div>
            <div class="legend-note">Arrow direction shows the destination team. Hover over an edge for player and salary.</div>
        </div>
        <script>
            function resizeNetworkCanvas() {
                const container = document.getElementById("mynetwork");

                if (!container) {
                    return;
                }

                container.style.width = window.innerWidth + "px";
                container.style.height = window.innerHeight + "px";

                network.setSize(
                    window.innerWidth + "px",
                    window.innerHeight + "px"
                );
                network.redraw();
            }

            window.addEventListener("load", function () {
                resizeNetworkCanvas();

                // Wait until logos and browser layout have settled.
                setTimeout(function () {
                    resizeNetworkCanvas();
                    network.fit({
                        animation: false
                    });
                }, 200);
            });

            window.addEventListener("resize", function () {
                resizeNetworkCanvas();
            });
        </script>
        </body>
        """,
    )

    output_path.write_text(html, encoding="utf-8")


def save_tables(
    output_dir: Path,
    records: list[TransactionRecord],
    movements: list[Movement],
    unresolved: list[dict[str, str]],
    unresolved_salaries: list[dict[str, str]],
) -> None:
    output_dir.mkdir(parents=True, exist_ok=True)
    pd.DataFrame([asdict(record) for record in records]).to_csv(
        output_dir / "raw_transactions.csv", index=False
    )
    pd.DataFrame([asdict(movement) for movement in movements]).to_csv(
        output_dir / "movements.csv", index=False
    )
    pd.DataFrame(unresolved).to_csv(
        output_dir / "unresolved_signings.csv", index=False
    )
    pd.DataFrame(unresolved_salaries).to_csv(
        output_dir / "unresolved_salaries.csv", index=False
    )


def build_browser_context(
    playwright,
    headed: bool,
    user_data_dir: Path | None,
) -> tuple[BrowserContext, object | None]:
    common_args = {
        "headless": not headed,
        "viewport": {"width": 1500, "height": 1000},
        "user_agent": (
            "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
            "(KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36"
        ),
        "locale": "en-US",
    }

    if user_data_dir is not None:
        user_data_dir.mkdir(parents=True, exist_ok=True)
        context = playwright.chromium.launch_persistent_context(
            str(user_data_dir), **common_args
        )
        return context, None

    browser = playwright.chromium.launch(headless=not headed)
    context = browser.new_context(
        viewport=common_args["viewport"],
        user_agent=common_args["user_agent"],
        locale=common_args["locale"],
    )
    return context, browser


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--headed",
        action="store_true",
        help="Show Chromium; useful if Spotrac challenges headless browsers.",
    )
    parser.add_argument(
        "--refresh",
        action="store_true",
        help="Ignore cached rendered HTML and download all pages again.",
    )
    parser.add_argument(
        "--cache-dir",
        type=Path,
        default=Path("spotrac_cache"),
        help="Directory for cached rendered HTML.",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("output"),
        help="Directory for CSV, PNG and HTML outputs.",
    )
    parser.add_argument(
        "--user-data-dir",
        type=Path,
        default=None,
        help="Persistent Chromium profile, useful for retaining challenge cookies.",
    )
    parser.add_argument(
        "--overrides",
        type=Path,
        default=None,
        help='Optional JSON mapping, e.g. {"Player Name": "LAL"}.',
    )
    parser.add_argument(
        "--salary-overrides",
        type=Path,
        default=None,
        help=(
            "Optional JSON mapping of player names to 2026-27 salary in dollars, "
            'e.g. {"Player Name": 18125000}.'
        ),
    )
    parser.add_argument(
        "--logo-cache-dir",
        type=Path,
        default=Path("nba_logo_cache"),
        help="Directory for official NBA team logos used by the static graph.",
    )
    parser.add_argument(
        "--layout-restarts",
        type=int,
        default=24,
        help="Number of force-directed candidates evaluated per connected component.",
    )
    parser.add_argument(
        "--layout-refinement-steps",
        type=int,
        default=1200,
        help="Local optimization steps used to reduce crossings and edge/logo conflicts.",
    )
    parser.add_argument(
        "--static-label-count",
        type=int,
        default=12,
        help=(
            "Number of highest-salary movements permanently labelled in the PNG. "
            "Use 0 for no permanent edge labels."
        ),
    )
    parser.add_argument(
        "--interactive-label-count",
        type=int,
        default=0,
        help=(
            "Number of highest-salary movements permanently labelled in HTML. "
            "All other players remain available on hover."
        ),
    )
    parser.add_argument(
        "--interactive-team-label-vadjust",
        type=float,
        default=-8.0,
        help=(
            "Vertical adjustment for team abbreviations in the interactive HTML. "
            "Negative values move labels upward toward their logos."
        ),
    )
    parser.add_argument(
        "--static-team-label-offset",
        type=float,
        default=-22.0,
        help=(
            "Vertical label offset in points for team abbreviations in the PNG. "
            "Values closer to zero move labels upward toward their logos."
        ),
    )
    parser.add_argument(
        "--interactive-edge-node-gap",
        type=float,
        default=8.0,
        help=(
            "Extra canvas-unit gap between each visible interactive edge endpoint "
            "and the team logo. Edges use transparent anchor nodes rather than "
            "the logo centres."
        ),
    )
    parser.add_argument(
        "--interactive-parallel-edge-spacing",
        type=float,
        default=13.0,
        help=(
            "Canvas-unit separation between neighbouring interactive edges that "
            "connect the same two teams. The endpoint anchors are fanned sideways, "
            "so the separation is visible even close to the team logos."
        ),
    )
    parser.add_argument(
        "--interactive-edge-hover-width",
        type=float,
        default=10.0,
        help=(
            "Width of an invisible mouse-target corridor behind each interactive "
            "edge. This makes low-salary thin lines easier to hover without "
            "changing their visible salary-based width."
        ),
    )
    parser.add_argument(
        "--request-pause",
        type=float,
        default=1.5,
        help="Seconds to pause between uncached Spotrac page requests.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    overrides = load_overrides(args.overrides)
    salary_overrides = load_salary_overrides(args.salary_overrides)
    cached_drafted_players = load_drafted_players(args.cache_dir)
    cached_drafted_players |= load_drafted_players_from_raw_transactions(args.output_dir)
    profile_html_cache: dict[str, str] = {}

    with sync_playwright() as playwright:
        context, browser = build_browser_context(
            playwright, args.headed, args.user_data_dir
        )
        page = context.pages[0] if context.pages else context.new_page()
        try:
            cached_records = (
                []
                if args.refresh
                else load_cached_transaction_records(args.output_dir)
            )
            transaction_start_date = determine_transaction_start_date(
                cached_records,
                refresh=args.refresh,
            )

            # The recent transaction listing is always fetched fresh. Profile and
            # other detail pages still use their caches, except for players present
            # in this fresh transaction tail.
            fetched_records = scrape_transactions(
                page,
                cache_dir=args.cache_dir,
                refresh=True,
                request_pause=args.request_pause,
                start_date=transaction_start_date,
                end_date=END_DATE,
            )
            records = (
                fetched_records
                if args.refresh
                else merge_transaction_records(
                    cached_records,
                    fetched_records,
                    replace_from_date=transaction_start_date,
                )
            )
            fresh_player_keys = {
                canonical_player_name(record.player) for record in fetched_records
            }
            print(
                f"Loaded {len(cached_records)} cached records, fetched "
                f"{len(fetched_records)} records from {transaction_start_date} "
                f"through {END_DATE}, and retained {len(records)} unique records"
            )

            drafted_players = cached_drafted_players | drafted_player_keys(records)
            if drafted_players:
                save_drafted_players(args.cache_dir, drafted_players)
            signing_players = candidate_signing_players(
                records, excluded_players=drafted_players
            )
            free_agent_sources = scrape_free_agent_sources(
                page,
                candidate_players=signing_players,
                cache_dir=args.cache_dir,
                refresh=args.refresh,
                request_pause=args.request_pause,
            )
            movements, unresolved = build_movements(
                records,
                free_agent_sources=free_agent_sources,
                overrides=overrides,
                drafted_players=drafted_players,
            )

            # Some signings are inbound-only on the transaction pages and are not
            # present on Spotrac's former-team free-agent index. Resolve only those
            # remaining players from their previous-season profile tables.
            if unresolved:
                print(
                    f"Checking previous-season teams for {len(unresolved)} "
                    "unresolved inbound signing(s)"
                )
                (
                    previous_season_sources,
                    profile_drafted_players,
                ) = scrape_previous_season_sources(
                    page,
                    unresolved_signings=unresolved,
                    cache_dir=args.cache_dir,
                    refresh=args.refresh,
                    request_pause=args.request_pause,
                    profile_html_cache=profile_html_cache,
                    refresh_player_keys=fresh_player_keys,
                )
                if profile_drafted_players:
                    drafted_players |= profile_drafted_players
                    save_drafted_players(args.cache_dir, drafted_players)

                if previous_season_sources or profile_drafted_players:
                    # Existing team-specific free-agent matches remain authoritative;
                    # previous-season profile data is a fallback only.
                    combined_sources = dict(previous_season_sources)
                    combined_sources.update(free_agent_sources)
                    movements, unresolved = build_movements(
                        records,
                        free_agent_sources=combined_sources,
                        overrides=overrides,
                        drafted_players=drafted_players,
                    )

            movements = collapse_player_movements(movements)
            rankings_salaries = scrape_salary_rankings(
                page,
                cache_dir=args.cache_dir,
                refresh=True,
                request_pause=args.request_pause,
            )

            print(f"Resolving {SALARY_SEASON} salaries for {len(movements)} movements")
            movements, unresolved_salaries = scrape_movement_salaries(
                page,
                movements,
                salary_overrides=salary_overrides,
                rankings_salaries=rankings_salaries,
                cache_dir=args.cache_dir,
                refresh=args.refresh,
                request_pause=args.request_pause,
                profile_html_cache=profile_html_cache,
                refresh_player_keys=fresh_player_keys,
            )
        finally:
            context.close()
            if browser is not None:
                browser.close()

    graph = movement_graph(movements)
    positions = compute_team_layout(
        graph,
        restarts=max(args.layout_restarts, 1),
        refinement_steps=max(args.layout_refinement_steps, 0),
    )

    save_tables(
        args.output_dir,
        records,
        movements,
        unresolved,
        unresolved_salaries,
    )
    draw_static_graph(
        graph,
        positions,
        args.output_dir / "nba_summer_transactions.png",
        args.logo_cache_dir,
        maximum_labels=max(args.static_label_count, 0),
        team_label_offset_points=args.static_team_label_offset,
    )
    draw_interactive_graph(
        graph,
        positions,
        args.output_dir / "nba_summer_transactions.html",
        maximum_labels=max(args.interactive_label_count, 0),
        endpoint_gap=max(args.interactive_edge_node_gap, 0.0),
        parallel_edge_spacing=max(args.interactive_parallel_edge_spacing, 0.0),
        hover_target_width=max(args.interactive_edge_hover_width, 0.0),
        team_label_vadjust=args.interactive_team_label_vadjust,
    )

    trade_count = sum(movement.move_type == "trade" for movement in movements)
    free_agent_count = len(movements) - trade_count
    print(
        f"Created {len(movements)} movements: {trade_count} trades and "
        f"{free_agent_count} free-agent/waiver signings."
    )
    print(f"Unresolved signings: {len(unresolved)}")
    print(f"Unresolved salaries: {len(unresolved_salaries)}")
    print(f"Outputs written to: {args.output_dir.resolve()}")


if __name__ == "__main__":
    main()
