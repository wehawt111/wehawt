"""Local HOTU match demo analyzer. Runs on localhost; uploaded demos stay local."""
from __future__ import annotations

import json
import math
import mimetypes
import os
import shutil
import sqlite3
import sys
import tempfile
import traceback
from bisect import bisect_left
from datetime import datetime, timezone
from collections import Counter, defaultdict
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, urlparse

HERE = Path(__file__).resolve().parent
WORK_PACKAGES = HERE.parents[1] / "work" / "demoparser_pkgs"
if WORK_PACKAGES.exists():
    sys.path.insert(0, str(WORK_PACKAGES))

try:
    from demoparser2 import DemoParser
except ImportError:
    DemoParser = None

MAX_UPLOAD = 1_600_000_000
HOTU_PLAYER_HINTS = {"dwushka", "frontales", "n0rb3r7", "norbert", "kade0", "mizu"}
DB_PATH = HERE / "matchroom.sqlite3"


def rows(frame):
    """Convert pandas/polars frames emitted by demoparser2 to dictionaries."""
    if hasattr(frame, "to_dicts"):
        return frame.to_dicts()
    return frame.to_dict(orient="records")


def safe_text(value, fallback=""):
    return fallback if value is None else str(value)


def analyze_demo(path: Path, hotu_team_number: int, opponent: str):
    if DemoParser is None:
        raise RuntimeError("Не установлен demoparser2. Выполните установку из requirements.txt.")
    parser = DemoParser(str(path))
    header = parser.parse_header()
    map_name = safe_text(header.get("map_name"), "unknown").removeprefix("de_")
    map_name = {"dust2": "Dust2"}.get(map_name.lower(), map_name[:1].upper() + map_name[1:])
    roster_rows = rows(parser.parse_player_info())
    player_team = {str(r.get("steamid")): int(r.get("team_number") or 0) for r in roster_rows}
    player_names = {str(r.get("steamid")): safe_text(r.get("name")) for r in roster_rows}
    roster_votes = Counter()
    for r in roster_rows:
        normalized = safe_text(r.get("name")).casefold().replace("_", "")
        if normalized in {n.replace("_", "") for n in HOTU_PLAYER_HINTS}:
            team = int(r.get("team_number") or 0)
            if team in (2, 3):
                roster_votes[team] += 1
    if roster_votes and max(roster_votes.values()) >= 3:
        hotu_team_number = roster_votes.most_common(1)[0][0]
        team_detection = f"Состав HOTU определён по демо: {roster_votes[hotu_team_number]} игроков"
    else:
        team_detection = f"Автоопределение состава не сработало; использована команда {hotu_team_number} из настройки"
    player_team["0"] = 0

    starts = rows(parser.parse_event("round_announce_match_start"))
    start_tick = max((int(r.get("tick") or 0) for r in starts), default=0)
    ends = [r for r in rows(parser.parse_event("round_end")) if int(r.get("tick") or 0) > start_tick and r.get("winner") in ("CT", "T")]
    ends.sort(key=lambda r: int(r.get("tick") or 0))
    if not ends:
        raise ValueError("В демо не найдены завершённые игровые раунды.")

    deaths = [r for r in rows(parser.parse_event("player_death", player=["team_name", "CCSPlayerPawn.m_szLastPlaceName"])) if int(r.get("tick") or 0) > start_tick]
    # player_hurt records exact health/armor damage and weapon attribution. Flash
    # blindness is not emitted by every HLTV demo/parser build, so keep it optional.
    try:
        hurt_events = [r for r in rows(parser.parse_event("player_hurt")) if int(r.get("tick") or 0) > start_tick]
    except Exception:
        hurt_events = []
    try:
        blind_events = rows(parser.parse_event("player_blind"))
    except Exception:
        blind_events = []
    plants = [r for r in rows(parser.parse_event("bomb_planted", player=["CCSPlayerPawn.m_szLastPlaceName", "X", "Y"])) if int(r.get("tick") or 0) > start_tick]
    defuses = [r for r in rows(parser.parse_event("bomb_defused")) if int(r.get("tick") or 0) > start_tick]

    def team_of(row, side="user"):
        return player_team.get(str(row.get(f"{side}_steamid") or "0"), 0)

    score = Counter()
    maps_rounds = []
    round_stats = []
    previous = start_tick
    map_round_by_number = {}
    for idx, ending in enumerate(ends, start=1):
        end_tick = int(ending["tick"])
        in_deaths = [d for d in deaths if previous < int(d.get("tick") or 0) <= end_tick]
        # The round winner field is the winning side. Resolve its team via players seen on that side.
        side_team = Counter()
        for d in in_deaths:
            for prefix in ("attacker", "user"):
                team = team_of(d, prefix)
                side = safe_text(d.get(f"{prefix}_team_name")).upper()
                side = "T" if side in ("TERRORIST", "T") else "CT" if side == "CT" else side
                if team in (2, 3) and side in ("CT", "T"):
                    side_team[(side, team)] += 1
        winner_side = safe_text(ending.get("winner")).upper()
        winner_side = "T" if winner_side in ("TERRORIST", "T") else "CT" if winner_side == "CT" else winner_side
        candidates = [(n, t) for (s, t), n in side_team.items() if s == winner_side]
        winner_team = max(candidates, default=(0, 0))[1]
        if winner_team == 0:
            # First half starts with fixed team number sides in standard CS demos; avoid guessing by assigning
            # the opponent only when winner is unresolvable and keep all other metrics available.
            winner_team = 0
        if winner_team in (2, 3):
            score[winner_team] += 1
        round_no = int(ending.get("round") or idx)
        map_round_by_number[round_no] = idx
        first_kill = None
        for d in in_deaths:
            attacker, victim = team_of(d, "attacker"), team_of(d, "user")
            if attacker in (2, 3) and victim in (2, 3) and attacker != victim:
                first_kill = (attacker, safe_text(d.get("user_CCSPlayerPawn.m_szLastPlaceName"), "Unknown"),
                              safe_text(d.get("attacker_name"), "unknown"), safe_text(d.get("user_name"), "unknown"), int(d.get("tick") or 0))
                break
        sides = {}
        for (side, team), count in side_team.items():
            if team in (2, 3) and count > side_team.get((sides.get(team), team), 0):
                sides[team] = side
        round_stats.append({"winner": winner_team, "first": first_kill, "start": previous, "end": end_tick, "deaths": in_deaths, "sides": sides})
        previous = end_tick

    def rounds_for_event(events):
        result = defaultdict(list)
        for event in events:
            tick = int(event.get("tick") or 0)
            for i, rr in enumerate(round_stats, start=1):
                if rr["start"] < tick <= rr["end"]:
                    result[i].append(event)
                    break
        return result

    hurt_by_round = rounds_for_event(hurt_events)
    blind_by_round = rounds_for_event(blind_events)

    plant_by_round = rounds_for_event(plants)
    defuse_by_round = rounds_for_event(defuses)
    team_names = {hotu_team_number: "HOTU", (5 - hotu_team_number): opponent}
    kills = Counter()
    plants_count = Counter()
    plant_wins = Counter()
    openers, open_wins = Counter(), Counter()
    zones = Counter()
    player_kills = Counter()
    for i, rr in enumerate(round_stats, start=1):
        for d in rr["deaths"]:
            a = team_of(d, "attacker")
            if a in (2, 3) and team_of(d, "user") in (2, 3) and a != team_of(d, "user"):
                kills[a] += 1
                player_kills[safe_text(d.get("attacker_name"), "unknown")] += 1
        if rr["first"]:
            team, zone = rr["first"][:2]
            openers[team] += 1
            zones[zone] += 1
            if rr["winner"] == team:
                open_wins[team] += 1
        for p in plant_by_round.get(i, []):
            team = team_of(p, "user")
            if team in (2, 3):
                plants_count[team] += 1
                if rr["winner"] == team:
                    plant_wins[team] += 1

    def ordered(counter):
        return [counter[hotu_team_number], counter[5 - hotu_team_number]]

    halves = [[0, 0], [0, 0]]
    for i, rr in enumerate(round_stats):
        if rr["winner"] in (2, 3):
            halves[min(i // 12, 1)][0 if rr["winner"] == hotu_team_number else 1] += 1
    half_side = []
    for half_idx in range(2):
        team_sides = Counter()
        for rr in round_stats[half_idx * 12:(half_idx + 1) * 12]:
            for d in rr["deaths"]:
                for prefix in ("attacker", "user"):
                    team = team_of(d, prefix)
                    side = safe_text(d.get(f"{prefix}_team_name")).upper()
                    side = "T" if side in ("TERRORIST", "T") else "CT" if side == "CT" else side
                    if team == hotu_team_number and side in ("CT", "T"):
                        team_sides[side] += 1
        side_label = "CT" if team_sides["CT"] > team_sides["T"] else "T"
        half_side.append(f"HOTU · {side_label}")
    # In regulation CS2, pistol rounds are the opening round of each half.
    pistol_rounds = []
    for round_number in (1, 13):
        if round_number > len(round_stats):
            continue
        rr = round_stats[round_number - 1]
        side = rr["sides"].get(hotu_team_number)
        if side not in ("CT", "T"):
            side = "CT" if half_side[(round_number - 1) // 12].endswith("CT") else "T"
        winner = "HOTU" if rr["winner"] == hotu_team_number else opponent if rr["winner"] == 5 - hotu_team_number else "не определён"
        first = rr["first"]
        plant = next((p for p in plant_by_round.get(round_number, []) if team_of(p, "user") in (hotu_team_number, 5 - hotu_team_number)), None)
        site = safe_text(plant.get("user_CCSPlayerPawn.m_szLastPlaceName")).removeprefix("Bombsite") if plant else None
        next_winner = round_stats[round_number]["winner"] if round_number < len(round_stats) else None
        pistol_rounds.append({
            "round": round_number, "hotuSide": side, "winner": winner,
            "firstKillTeam": "HOTU" if first and first[0] == hotu_team_number else opponent if first else None,
            "firstKiller": first[2] if first else None, "firstVictim": first[3] if first else None,
            "plantSite": site,
            "nextRoundWinner": "HOTU" if next_winner == hotu_team_number else opponent if next_winner == 5 - hotu_team_number else "не определён" if next_winner is not None else None,
        })
    pistol_analysis = {
        "count": len(pistol_rounds), "wins": sum(r["winner"] == "HOTU" for r in pistol_rounds),
        "sideWins": {side: sum(r["hotuSide"] == side and r["winner"] == "HOTU" for r in pistol_rounds) for side in ("T", "CT")},
        "rounds": pistol_rounds,
    }
    utility = {}
    utility_names = (("smokegrenade_detonate", "smoke", "Дым"), ("flashbang_detonate", "flash", "Флешка"), ("hegrenade_detonate", "he", "HE"), ("inferno_startburn", "molly", "Молотов"))
    utility_events = {}
    for event_name, key, _label in utility_names:
        try:
            utility_events[key] = [e for e in rows(parser.parse_event(event_name, player=["CCSPlayerPawn.m_szLastPlaceName", "team_name", "team_num"])) if int(e.get("tick") or 0) > start_tick]
            utility[key] = len(utility_events[key])
        except Exception:
            utility_events[key] = []
            utility[key] = 0

    # Opponent tendencies are descriptive patterns across rounds. Coordinate clusters are
    # grenade detonation cells, not named callouts or proof of a deliberate lineup.
    opponent_team = 5 - hotu_team_number
    freeze_events = rows(parser.parse_event("round_freeze_end"))
    valid_freeze_events = [e for e in freeze_events if int(e.get("tick") or 0) >= start_tick]
    freeze_by_round = rounds_for_event(valid_freeze_events)
    # The official first live round can start on the exact match-start tick.
    for event in valid_freeze_events:
        if int(event.get("tick") or 0) == start_tick:
            freeze_by_round[1].append(event)
    attack_rounds = [i for i, rr in enumerate(round_stats, start=1) if rr["sides"].get(opponent_team) in ("T", "TERRORIST")]
    attack_wins = sum(round_stats[i - 1]["winner"] == opponent_team for i in attack_rounds)
    defense_rounds = [i for i, rr in enumerate(round_stats, start=1) if rr["sides"].get(opponent_team) == "CT"]
    defense_wins = sum(round_stats[i - 1]["winner"] == opponent_team for i in defense_rounds)
    opponent_openings = [rr for i, rr in enumerate(round_stats, start=1)
                         if i in attack_rounds and rr["first"] and rr["first"][0] == opponent_team]
    opponent_open_wins = sum(rr["winner"] == opponent_team for rr in opponent_openings)
    opponent_zones = Counter(rr["first"][1] for rr in opponent_openings)
    entry_attempts = Counter(rr["first"][2] for rr in opponent_openings)
    entry_wins = Counter(rr["first"][2] for rr in opponent_openings if rr["winner"] == opponent_team)
    hotu_first_victims = Counter(rr["first"][3] for rr in opponent_openings)
    defense_openings = [rr for rr in round_stats if rr["sides"].get(opponent_team) == "CT" and rr["first"] and rr["first"][0] == opponent_team]
    defense_entry_wins = sum(rr["winner"] == opponent_team for rr in defense_openings)
    defense_zones = Counter(rr["first"][1] for rr in defense_openings)
    defense_entry_players = Counter(rr["first"][2] for rr in defense_openings)
    hotu_plants_allowed = defaultdict(lambda: {"plants": 0, "hotuWins": 0})
    sites = defaultdict(lambda: {"plants": 0, "wins": 0})
    for i, rr in enumerate(round_stats, start=1):
        for plant in plant_by_round.get(i, []):
            raw_site = safe_text(plant.get("user_CCSPlayerPawn.m_szLastPlaceName"))
            site = raw_site.removeprefix("Bombsite") or "Unknown"
            if team_of(plant, "user") == opponent_team:
                sites[site]["plants"] += 1
                sites[site]["wins"] += int(rr["winner"] == opponent_team)
            elif team_of(plant, "user") == hotu_team_number and rr["sides"].get(opponent_team) == "CT":
                hotu_plants_allowed[site]["plants"] += 1
                hotu_plants_allowed[site]["hotuWins"] += int(rr["winner"] == hotu_team_number)

    nade_patterns = []
    utility_round_events = {key: rounds_for_event(events) for key, events in utility_events.items()}
    freeze_tick_by_round = {i: int(items[0].get("tick") or 0) for i, items in freeze_by_round.items() if items}
    utility_player_counts = Counter()
    for event_key, _key, label in utility_names:
        # Key names align with the utility buckets above.
        key = next(k for name, k, _ in utility_names if name == event_key)
        events_by_round = utility_round_events[key]
        opponent_events = []
        spot_rounds = defaultdict(set)
        spot_counts = Counter()
        early_events = 0
        for i, rr in enumerate(round_stats, start=1):
            if rr["sides"].get(opponent_team) not in ("T", "TERRORIST"):
                continue
            for event in events_by_round.get(i, []):
                if team_of(event, "user") != opponent_team:
                    continue
                opponent_events.append(event)
                utility_player_counts[safe_text(event.get("user_name"), "unknown")] += 1
                offset = max(0, int(event.get("tick") or 0) - freeze_tick_by_round.get(i, rr["start"])) / 64.0
                if offset <= 25:
                    early_events += 1
                x, y = event.get("x"), event.get("y")
                if x is not None and y is not None:
                    cell = (int(round(float(x) / 256) * 256), int(round(float(y) / 256) * 256))
                    spot_rounds[cell].add(i)
                    spot_counts[cell] += 1
        common_spots = [{"x": cell[0], "y": cell[1], "rounds": len(rnds), "events": spot_counts[cell]}
                        for cell, rnds in sorted(spot_rounds.items(), key=lambda item: (len(item[1]), spot_counts[item[0]]), reverse=True)
                        if len(rnds) >= 3][:3]
        nade_patterns.append({"type": label, "count": len(opponent_events),
                              "perAttackRound": round(len(opponent_events) / len(attack_rounds), 2) if attack_rounds else 0,
                              "earlyCount": early_events, "earlyWindowSeconds": 25, "commonSpots": common_spots})

    defense_nades = []
    defense_utility_players = Counter()
    for _event_name, key, label in utility_names:
        events_by_round = utility_round_events[key]
        opponent_events, early_events = [], 0
        spot_rounds, spot_counts = defaultdict(set), Counter()
        for i in defense_rounds:
            rr = round_stats[i - 1]
            for event in events_by_round.get(i, []):
                if team_of(event, "user") != opponent_team:
                    continue
                opponent_events.append(event)
                defense_utility_players[safe_text(event.get("user_name"), "unknown")] += 1
                offset = max(0, int(event.get("tick") or 0) - freeze_tick_by_round.get(i, rr["start"])) / 64.0
                if offset <= 25:
                    early_events += 1
                x, y = event.get("x"), event.get("y")
                if x is not None and y is not None:
                    cell = (int(round(float(x) / 256) * 256), int(round(float(y) / 256) * 256))
                    spot_rounds[cell].add(i)
                    spot_counts[cell] += 1
        common_spots = [{"x": cell[0], "y": cell[1], "rounds": len(rnds), "events": spot_counts[cell]}
                        for cell, rnds in sorted(spot_rounds.items(), key=lambda item: (len(item[1]), spot_counts[item[0]]), reverse=True)
                        if len(rnds) >= 3][:3]
        defense_nades.append({"type": label, "count": len(opponent_events),
                              "perDefenseRound": round(len(opponent_events) / len(defense_rounds), 2) if defense_rounds else 0,
                              "earlyCount": early_events, "earlyWindowSeconds": 25, "commonSpots": common_spots})

    opponent_blinds = {"blinds": 0, "blindSeconds": 0.0, "blindSecondsOnHOTU": 0.0, "opponentsBlinded": 0,
                       "players": defaultdict(lambda: {"blinds": 0, "blindSeconds": 0.0, "opponentsBlinded": 0})}
    for event in blind_events:
        attacker_team, victim_team = team_of(event, "attacker"), team_of(event, "user")
        if attacker_team != opponent_team:
            continue
        try:
            duration = max(0.0, float(event.get("blind_duration") or 0))
        except (TypeError, ValueError):
            duration = 0.0
        name = safe_text(event.get("attacker_name"), "unknown")
        opponent_blinds["blinds"] += 1
        opponent_blinds["blindSeconds"] += duration
        data = opponent_blinds["players"][name]
        data["blinds"] += 1
        data["blindSeconds"] += duration
        if victim_team == hotu_team_number:
            opponent_blinds["opponentsBlinded"] += 1
            opponent_blinds["blindSecondsOnHOTU"] += duration
            data["opponentsBlinded"] += 1
            data["blindSecondsOnHOTU"] = data.get("blindSecondsOnHOTU", 0.0) + duration
    opponent_flash_report = {"available": bool(blind_events), "blinds": opponent_blinds["blinds"],
        "blindSeconds": round(opponent_blinds["blindSeconds"], 1), "blindSecondsOnHOTU": round(opponent_blinds["blindSecondsOnHOTU"], 1),
        "opponentsBlinded": opponent_blinds["opponentsBlinded"],
        "players": [{"name": name, **{**data, "blindSeconds": round(data["blindSeconds"], 1)}}
                    for name, data in sorted(opponent_blinds["players"].items(), key=lambda item: item[1]["opponentsBlinded"], reverse=True)[:8]]}

    opponent_damage_dealt = 0
    opponent_damage_to_hotu = 0
    opponent_utility_damage = 0
    opponent_damage_players = defaultdict(lambda: {"healthDamage": 0, "utilityDamage": 0, "hits": 0})
    opponent_damage_weapons = Counter()
    for event in hurt_events:
        if team_of(event, "attacker") != opponent_team:
            continue
        try:
            damage_value = max(0, int(event.get("dmg_health") or 0))
        except (TypeError, ValueError):
            damage_value = 0
        weapon = safe_text(event.get("weapon"), "unknown")
        player = safe_text(event.get("attacker_name"), "unknown")
        opponent_damage_dealt += damage_value
        opponent_damage_weapons[weapon] += damage_value
        opponent_damage_players[player]["healthDamage"] += damage_value
        opponent_damage_players[player]["hits"] += 1
        if team_of(event, "user") == hotu_team_number:
            opponent_damage_to_hotu += damage_value
        if any(token in weapon.casefold() for token in ("hegrenade", "molotov", "incgrenade", "inferno", "firebomb")):
            opponent_utility_damage += damage_value
            opponent_damage_players[player]["utilityDamage"] += damage_value
    opponent_damage_report = {
        "healthDamage": opponent_damage_dealt, "damageToHOTU": opponent_damage_to_hotu,
        "utilityHealthDamage": opponent_utility_damage, "hits": sum(v["hits"] for v in opponent_damage_players.values()),
        "players": [{"name": name, **data} for name, data in sorted(opponent_damage_players.items(), key=lambda item: item[1]["healthDamage"], reverse=True)[:8]],
        "weapons": [{"name": name, "healthDamage": damage} for name, damage in opponent_damage_weapons.most_common(8)],
        "flashBlindnessAvailable": bool(blind_events), "flash": opponent_flash_report,
    }

    opponent_patterns = {
        "attackRounds": len(attack_rounds), "attackWins": attack_wins,
        "openingRounds": len(opponent_openings), "openingWins": opponent_open_wins,
        "openingZones": [[name, count] for name, count in opponent_zones.most_common(5)],
        "entryPlayers": [{"name": name, "openings": count, "wins": entry_wins[name]}
                         for name, count in entry_attempts.most_common(5)],
        "hotuFirstVictims": [[name, count] for name, count in hotu_first_victims.most_common(5)],
        "utilityPlayers": [{"name": name, "detonations": count} for name, count in utility_player_counts.most_common(5)],
        "plantSites": [{"site": name, **data} for name, data in sorted(sites.items(), key=lambda item: item[1]["plants"], reverse=True)],
        "nades": nade_patterns,
        "damage": opponent_damage_report,
        "defense": {
            "rounds": len(defense_rounds), "wins": defense_wins,
            "openingRounds": len(defense_openings), "openingWins": defense_entry_wins,
            "openingZones": [[name, count] for name, count in defense_zones.most_common(5)],
            "entryPlayers": [{"name": name, "openings": count,
                              "wins": sum(rr["winner"] == opponent_team for rr in defense_openings if rr["first"][2] == name)}
                             for name, count in defense_entry_players.most_common(5)],
            "plantsAllowed": sum(x["plants"] for x in hotu_plants_allowed.values()),
            "hotuWinsAfterPlant": sum(x["hotuWins"] for x in hotu_plants_allowed.values()),
            "plantSitesAllowed": [{"site": name, **data} for name, data in sorted(hotu_plants_allowed.items(), key=lambda item: item[1]["plants"], reverse=True)],
            "nades": defense_nades,
            "utilityPlayers": [{"name": name, "detonations": count} for name, count in defense_utility_players.most_common(5)],
        },
        "rounds": [],
    }
    for i in attack_rounds:
        rr = round_stats[i - 1]
        plant = next((p for p in plant_by_round.get(i, []) if team_of(p, "user") == opponent_team), None)
        plant_site = safe_text(plant.get("user_CCSPlayerPawn.m_szLastPlaceName")).removeprefix("Bombsite") if plant else "—"
        plant_tick = int(plant.get("tick") or 0) if plant else 0
        freeze_tick = freeze_tick_by_round.get(i, rr["start"])
        grenade_counts = {}
        for _event_name, key, label in utility_names:
            grenade_counts[label] = sum(team_of(e, "user") == opponent_team for e in utility_round_events[key].get(i, []))
        opening = "соперник" if rr["first"] and rr["first"][0] == opponent_team else "HOTU" if rr["first"] else "без первого фрага"
        opponent_patterns["rounds"].append({
            "round": i,
            "result": "победа" if rr["winner"] == opponent_team else "поражение" if rr["winner"] == hotu_team_number else "не определён",
            "opening": opening,
            "opener": rr["first"][2] if rr["first"] and rr["first"][0] == opponent_team else None,
            "firstVictim": rr["first"][3] if rr["first"] and rr["first"][0] == opponent_team else None,
            "plantSite": plant_site,
            "plantSeconds": round((plant_tick - freeze_tick) / 64, 1) if plant_tick and 0 <= (plant_tick - freeze_tick) / 64 <= 120 else None,
            "nades": grenade_counts,
        })

    # Round-by-round packet: facts from events plus clearly labelled tactical hypotheses.
    site_positions = defaultdict(list)
    for event in plants:
        place = safe_text(event.get("user_CCSPlayerPawn.m_szLastPlaceName")).casefold()
        site = "A" if "bombsitea" in place else "B" if "bombsiteb" in place else None
        x, y = event.get("user_X"), event.get("user_Y")
        if site and x is not None and y is not None:
            try:
                site_positions[site].append((float(x), float(y)))
            except (TypeError, ValueError):
                pass
    site_centers = {site: (sum(x for x, _ in points) / len(points), sum(y for _, y in points) / len(points))
                    for site, points in site_positions.items() if points}

    freeze_tick_by_round = {i: int(items[0].get("tick") or 0) for i, items in freeze_by_round.items() if items}
    snapshot_ticks = {}
    trajectory_tick_round = {}
    for i, rr in enumerate(round_stats, start=1):
        freeze_tick = freeze_tick_by_round.get(i)
        if freeze_tick is None:
            freeze_tick = rr["start"]
        contact_tick = rr["first"][4] if rr["first"] else freeze_tick + 20 * 64
        contact_tick = min(max(contact_tick - 5 * 64, freeze_tick), rr["end"])
        # round_start is the prior round_end boundary. Two ticks later, the
        # awarded money is visible and the next buy phase has not begun.
        prebuy_tick = 1 if i == 1 and start_tick > 1 else rr["start"] + 2
        snapshot_ticks[i] = {"prebuy": prebuy_tick, "buy": freeze_tick, "contact": contact_tick}
        # Coarse live-play samples for player movement; avoid implying frame-by-frame precision.
        first_live_tick = freeze_tick + 2 * 64
        for tick in range(first_live_tick, rr["end"] + 1, 5 * 64):
            trajectory_tick_round[tick] = i
    requested_ticks = sorted({tick for round_ticks in snapshot_ticks.values() for tick in round_ticks.values() if tick > 0} | set(trajectory_tick_round))
    snapshots_by_tick = defaultdict(list)
    player_tracks = defaultdict(list)
    if requested_ticks:
        try:
            snapshots = rows(parser.parse_ticks(
                ["X", "Y", "team_num", "is_alive", "last_place_name", "active_weapon_name", "balance",
                 "current_equip_value", "round_start_equip_value", "inventory", "armor", "has_helmet", "has_defuser"],
                ticks=requested_ticks))
            for state in snapshots:
                tick = int(state.get("tick") or 0)
                snapshots_by_tick[tick].append(state)
                round_no = trajectory_tick_round.get(tick)
                if round_no is None or not state.get("is_alive"):
                    continue
                steamid = str(state.get("steamid") or "")
                team = player_team.get(steamid)
                if team not in (hotu_team_number, opponent_team):
                    continue
                try:
                    x, y = float(state.get("X")), float(state.get("Y"))
                    if not (math.isfinite(x) and math.isfinite(y)):
                        continue
                except (TypeError, ValueError, NameError):
                    continue
                rr = round_stats[round_no - 1]
                freeze_tick = freeze_tick_by_round.get(round_no, rr["start"])
                player_tracks[steamid].append({"round": round_no,
                    "seconds": round(max(0, tick - freeze_tick) / 64, 1),
                    "x": round(x, 1), "y": round(y, 1),
                    "area": safe_text(state.get("last_place_name"), "")})
        except Exception:
            snapshots_by_tick = defaultdict(list)
            player_tracks = defaultdict(list)

    grenade_tracks = []
    try:
        grenade_frame = parser.parse_grenades()
        if hasattr(grenade_frame, "dropna") and all(c in grenade_frame.columns for c in ("tick", "x", "y", "z", "grenade_entity_id", "steamid", "grenade_type")):
            grenade_frame = grenade_frame.dropna(subset=["tick", "x", "y", "z"]).sort_values("tick")
            round_ends = [rr["end"] for rr in round_stats]
            group_cols = ["grenade_entity_id", "steamid", "grenade_type"]
            for (entity_id, steamid_raw, grenade_type_raw), frame in grenade_frame.groupby(group_cols, sort=False, dropna=False):
                sid = str(int(steamid_raw)) if isinstance(steamid_raw, (int, float)) and math.isfinite(float(steamid_raw)) else str(steamid_raw)
                team_number = player_team.get(sid)
                if team_number not in (hotu_team_number, opponent_team):
                    continue
                samples = frame[["tick", "x", "y", "z"]].to_numpy()
                episode = []
                episode_round = None
                previous_tick = None

                def flush_grenade_episode():
                    if len(episode) < 2 or episode_round is None:
                        return
                    stride = max(1, math.ceil(len(episode) / 44))
                    kept = episode[::stride]
                    if kept[-1] is not episode[-1]:
                        kept.append(episode[-1])
                    round_start = freeze_tick_by_round.get(episode_round, round_stats[episode_round - 1]["start"])
                    grenade_tracks.append({
                        "round": episode_round,
                        "entityId": int(entity_id) if isinstance(entity_id, (int, float)) and math.isfinite(float(entity_id)) else safe_text(entity_id),
                        "player": player_names.get(sid, safe_text(frame.iloc[0].get("name"), "unknown")) if hasattr(frame, "iloc") else player_names.get(sid, "unknown"),
                        "team": "HOTU" if team_number == hotu_team_number else opponent,
                        "type": safe_text(grenade_type_raw, "Grenade"),
                        "startSeconds": round(max(0, episode[0][0] - round_start) / 64, 2),
                        "endSeconds": round(max(0, episode[-1][0] - round_start) / 64, 2),
                        "points": [{"x": round(p[1], 1), "y": round(p[2], 1), "z": round(p[3], 1)} for p in kept],
                    })

                for row in samples:
                    tick = int(row[0])
                    round_index = bisect_left(round_ends, tick)
                    round_no = round_index + 1
                    if round_index >= len(round_stats) or tick <= round_stats[round_index]["start"]:
                        continue
                    if episode and (round_no != episode_round or tick - previous_tick > 10 * 64):
                        flush_grenade_episode()
                        episode = []
                    episode_round = round_no
                    episode.append((tick, float(row[1]), float(row[2]), float(row[3])))
                    previous_tick = tick
                flush_grenade_episode()
    except Exception as exc:
        print(f"[hotu] grenade paths unavailable: {exc}")

    primary_weapons = {"AK-47", "M4A4", "M4A1-S", "AWP", "SSG 08", "FAMAS", "Galil AR", "AUG", "SG 553",
                       "MP9", "MAC-10", "MP7", "MP5-SD", "UMP-45", "PP-Bizon", "P90", "Nova", "XM1014",
                       "MAG-7", "Sawed-Off", "M249", "Negev"}
    grenade_items = {"Smoke Grenade", "Flashbang", "High Explosive Grenade", "Molotov", "Incendiary Grenade"}

    def state_team(state):
        try:
            team = int(state.get("team_num") or 0)
        except (TypeError, ValueError):
            team = 0
        sid = str(state.get("steamid") or "")
        if team not in (2, 3) or sid not in player_team or not state.get("is_alive"):
            return None
        return team

    def team_loadout(team, states):
        players = []
        cash_available = 0
        cash_players = 0
        for state in states:
            try:
                snapshot_team = int(state.get("team_num") or 0)
            except (TypeError, ValueError):
                snapshot_team = 0
            sid = str(state.get("steamid") or "")
            if snapshot_team != team or sid not in player_team:
                continue
            inventory = state.get("inventory")
            if not isinstance(inventory, list):
                inventory = []
            inventory = [safe_text(item) for item in inventory if item]
            try:
                equip = int(state.get("current_equip_value") or 0)
            except (TypeError, ValueError):
                equip = 0
            try:
                balance_raw = state.get("balance")
                balance = int(balance_raw) if balance_raw is not None else None
                if balance is not None:
                    cash_available += balance
                    cash_players += 1
            except (TypeError, ValueError):
                balance = None
            players.append({"name": safe_text(state.get("name"), "игрок"), "equipmentValue": equip,
                            "cash": balance,
                            "primary": next((item for item in inventory if item in primary_weapons), None),
                            "armor": int(state.get("armor") or 0) > 0, "helmet": bool(state.get("has_helmet")),
                            "defuser": bool(state.get("has_defuser")),
                            "utility": [item for item in inventory if item in grenade_items]})
        primaries = sum(bool(p["primary"]) for p in players)
        total = sum(p["equipmentValue"] for p in players)
        avg = round(total / len(players)) if players else 0
        if primaries >= 4 and avg >= 3800:
            buy_type = "full"
        elif primaries >= 2 or avg >= 1800:
            buy_type = "force"
        else:
            buy_type = "eco"
        resource_total = total + cash_available
        return {"players": len(players), "cashPlayers": cash_players, "cashComplete": bool(players) and cash_players == len(players),
                "equipmentValue": total, "averageEquipment": avg, "cashRemaining": cash_available,
                "averageCashRemaining": round(cash_available / cash_players) if cash_players else 0,
                "resourceTotal": resource_total,
                "reserveShare": round(cash_available / resource_total, 3) if resource_total else 0,
                "primaryCount": primaries, "buyType": buy_type,
                "armorCount": sum(p["armor"] for p in players), "defuserCount": sum(p["defuser"] for p in players),
                "loadouts": players}

    def economy_assessment(team_buy, enemy_buy, pistol_round=False):
        if pistol_round:
            return {"label": "Стартовая пистолетка", "detail": "Регламентный пистолетный раунд: обычные правила выбора эко/форса/полного закупа здесь неприменимы.", "confidence": "факт раунда"}
        if not team_buy.get("players"):
            return {"label": "Нет снимка экономики", "detail": "Не удалось распознать состав или состояние закупа на freeze end.", "confidence": "нет данных"}
        ratio = (team_buy["equipmentValue"] / enemy_buy["equipmentValue"]
                 if enemy_buy and enemy_buy.get("equipmentValue") else None)
        team_buy["investmentRatioVsOpponent"] = round(ratio, 2) if ratio is not None else None
        relation = ("Инвестиция заметно ниже соперника" if ratio is not None and ratio < .7 else
                    "Инвестиция сопоставима с соперником" if ratio is not None and ratio <= 1.3 else
                    "Инвестиция выше соперника" if ratio is not None else "Сравнение с соперником недоступно")
        cash_note = (f"На руках после закупа ${team_buy['cashRemaining']:,} ({team_buy['cashPlayers']}/{team_buy['players']} игроков с данными). "
                     if team_buy.get("cashComplete") else "Остаток денег показан частично или без полного снимка. ")
        if team_buy["buyType"] == "full":
            if team_buy["cashComplete"] and team_buy["averageCashRemaining"] < 800:
                label = "Полный закуп с низким резервом"
                detail = "Команда собрала полноценные комплекты, но после закупа у большинства почти не осталось денег; при поражении вероятен смешанный закуп или эко."
            elif ratio is not None and ratio < .7:
                label = "Полный закуп, но слабее по инвестиции"
                detail = "У команды полный набор основных оружий, однако суммарная стоимость экипировки существенно ниже соперника. Проверьте AWP, броню, гранаты и сохранённое оружие."
            else:
                label = "Полный закуп"
                detail = "Есть не менее четырёх основных оружий и высокий средний уровень экипировки; сопоставьте сохранённый резерв с риском следующего раунда."
        elif team_buy["buyType"] == "force":
            if ratio is not None and ratio < .7:
                label = "Force против более дорогого закупа"
                detail = "Экипировка заметно уступает сопернику. Такой риск может быть осознанным, но по одному снимку нельзя подтвердить причину (серия поражений, plant, бонус за убийства или турнирный контекст)."
            elif team_buy["cashComplete"] and team_buy["averageCashRemaining"] < 800:
                label = "Смешанный закуп с низким резервом"
                detail = "Часть команды вложилась, но текущий состав оружия неоднороден и денег после закупа мало. Проверьте, синхронно ли закупились игроки и была ли цель сохранить деньги."
            else:
                label = "Force / смешанный закуп"
                detail = "Комплекты неоднородны. Проверьте, поддерживают ли дорогие оружия игроков с дешёвым закупом, и какой резерв остаётся на следующий раунд."
        else:
            if ratio is not None and ratio < .7:
                label = "Эко / лёгкий закуп против более дорогого"
                detail = "Команда существенно уступает по инвестиции. Сохранение денег может быть рациональным, если цель — общий полноценный закуп позже; текущего снимка недостаточно, чтобы определить намерение."
            else:
                label = "Эко / лёгкий закуп"
                detail = "Низкая инвестиция ограничивает возможности раунда. Проверьте, использовала ли команда дешёвые оружия для размена/сохранения и не смешала ли закуп с будущим сейвом."
        return {"label": label, "detail": detail + " " + relation + ". " + cash_note,
                "confidence": "эвристика по экипировке и остатку денег"}

    def nearest_site(x, y):
        if x is None or y is None or not site_centers:
            return None, None
        try:
            distances = {site: ((float(x) - cx) ** 2 + (float(y) - cy) ** 2) ** 0.5 for site, (cx, cy) in site_centers.items()}
        except (TypeError, ValueError):
            return None, None
        site, distance = min(distances.items(), key=lambda pair: pair[1])
        return (site, round(distance)) if distance <= 1800 else (None, round(distance))

    team_economy = {"HOTU": defaultdict(lambda: {"rounds": 0, "wins": 0}), opponent: defaultdict(lambda: {"rounds": 0, "wins": 0})}
    round_review = []
    for i, rr in enumerate(round_stats, start=1):
        hotu_side = rr["sides"].get(hotu_team_number)
        if hotu_side not in ("CT", "T"):
            hotu_side = "CT" if half_side[min((i - 1) // 12, len(half_side) - 1)].endswith("CT") else "T"
        opponent_side = "T" if hotu_side == "CT" else "CT"
        freeze_tick = freeze_tick_by_round.get(i, rr["start"])
        buy_states = snapshots_by_tick.get(snapshot_ticks.get(i, {}).get("buy", 0), [])
        contact_tick = snapshot_ticks.get(i, {}).get("contact", freeze_tick)
        contact_states = snapshots_by_tick.get(contact_tick, [])
        loadouts = {"HOTU": team_loadout(hotu_team_number, buy_states), opponent: team_loadout(opponent_team, buy_states)}
        prebuy_states = snapshots_by_tick.get(snapshot_ticks.get(i, {}).get("prebuy", 0), [])
        prebuy_loadouts = {"HOTU": team_loadout(hotu_team_number, prebuy_states),
                           opponent: team_loadout(opponent_team, prebuy_states)}
        for team_name in ("HOTU", opponent):
            actual = loadouts[team_name]
            budget = prebuy_loadouts[team_name]
            complete = budget["cashComplete"] and actual["cashComplete"] and budget["players"] == actual["players"]
            starting_by_player = {p["name"]: p["cash"] for p in budget["loadouts"]}
            for player in actual["loadouts"]:
                player["cashBeforePurchase"] = starting_by_player.get(player["name"])
                player["cashSpent"] = (player["cashBeforePurchase"] - player["cash"]
                                        if player["cashBeforePurchase"] is not None and player["cash"] is not None else None)
            actual["equipmentValueAtStart"] = budget["equipmentValue"] if budget["players"] == actual["players"] else None
            actual["resourcesBeforePurchase"] = (budget["cashRemaining"] + budget["equipmentValue"]
                                                  if complete else None)
            actual["equipmentValueChange"] = (actual["equipmentValue"] - budget["equipmentValue"]
                                               if budget["players"] == actual["players"] else None)
            actual["cashBeforePurchase"] = budget["cashRemaining"] if complete else None
            actual["purchaseSpend"] = (budget["cashRemaining"] - actual["cashRemaining"]
                                        if complete else None)
            actual["purchaseSpendComplete"] = complete
            actual["purchaseShare"] = (round(actual["purchaseSpend"] / budget["cashRemaining"], 3)
                                        if complete and budget["cashRemaining"] > 0 else None)
        if i in (1, 13):
            loadouts["HOTU"]["buyType"] = "pistol"
            loadouts[opponent]["buyType"] = "pistol"
        loadouts["HOTU"]["economyAssessment"] = economy_assessment(loadouts["HOTU"], loadouts[opponent], i in (1, 13))
        loadouts[opponent]["economyAssessment"] = economy_assessment(loadouts[opponent], loadouts["HOTU"], i in (1, 13))
        winner = "HOTU" if rr["winner"] == hotu_team_number else opponent if rr["winner"] == opponent_team else "не определён"
        for team_name, team_number in (("HOTU", hotu_team_number), (opponent, opponent_team)):
            if i in (1, 13):
                buy_type = "pistol"
            else:
                buy_type = loadouts[team_name]["buyType"]
            team_economy[team_name][buy_type]["rounds"] += 1
            team_economy[team_name][buy_type]["wins"] += int(rr["winner"] == team_number)

        kills_timeline = []
        for event in rr["deaths"]:
            attacker_team, victim_team = team_of(event, "attacker"), team_of(event, "user")
            if attacker_team not in (2, 3) or victim_team not in (2, 3) or attacker_team == victim_team:
                continue
            kills_timeline.append({"seconds": round(max(0, int(event.get("tick") or 0) - freeze_tick) / 64, 1),
                                   "killer": safe_text(event.get("attacker_name"), "unknown"),
                                   "killerTeam": "HOTU" if attacker_team == hotu_team_number else opponent,
                                   "victim": safe_text(event.get("user_name"), "unknown"),
                                   "victimTeam": "HOTU" if victim_team == hotu_team_number else opponent,
                                   "attackerTeamId": attacker_team, "victimTeamId": victim_team,
                                   "_tick": int(event.get("tick") or 0), "_victimSteamid": str(event.get("user_steamid") or "0"),
                                   "weapon": safe_text(event.get("weapon"), "unknown"),
                                   "location": safe_text(event.get("user_CCSPlayerPawn.m_szLastPlaceName"), "Unknown")})
        kills_timeline.sort(key=lambda event: event["seconds"])
        # Track the round's manpower after each death. This is an event-derived
        # state estimate; unknown/suicide deaths can make the starting 5v5 uncertain.
        alive = {hotu_team_number: min(5, sum(1 for t in player_team.values() if t == hotu_team_number)),
                 opponent_team: min(5, sum(1 for t in player_team.values() if t == opponent_team))}
        manpower = {}
        all_round_deaths = sorted(rr["deaths"], key=lambda d: int(d.get("tick") or 0))
        for death in all_round_deaths:
            victim_team = team_of(death, "user")
            attacker_team = team_of(death, "attacker")
            balance_before = alive[hotu_team_number] - alive[opponent_team]
            if victim_team in alive:
                alive[victim_team] = max(0, alive[victim_team] - 1)
            if attacker_team in alive and victim_team in alive and attacker_team != victim_team:
                balance = alive[hotu_team_number] - alive[opponent_team]
                manpower[(int(death.get("tick") or 0), str(death.get("user_steamid") or "0"))] = {
                    "hotuAlive": alive[hotu_team_number], "opponentAlive": alive[opponent_team],
                    "manpowerAdvantage": "HOTU" if balance > 0 else opponent if balance < 0 else "равно",
                    "balance": balance, "balanceBefore": balance_before,
                    "advantageSwing": ("HOTU восстановила равный состав" if balance_before < 0 <= balance else
                                       f"{opponent} восстановили равный состав" if balance_before > 0 >= balance else
                                       "HOTU получила численное преимущество" if balance_before <= 0 < balance else
                                       f"{opponent} получили численное преимущество" if balance_before >= 0 > balance else None),
                }
        for kill in kills_timeline:
            state = manpower.get((kill["_tick"], kill["_victimSteamid"]))
            if state:
                kill.update({k: state[k] for k in ("hotuAlive", "opponentAlive", "manpowerAdvantage", "balance", "balanceBefore", "advantageSwing")})
        for index, kill in enumerate(kills_timeline):
            previous_kill = kills_timeline[index - 1] if index else None
            trade = bool(previous_kill and kill["victim"] == previous_kill["killer"]
                         and kill["attackerTeamId"] == previous_kill["victimTeamId"]
                         and kill["victimTeamId"] == previous_kill["attackerTeamId"]
                         and kill["seconds"] - previous_kill["seconds"] <= 5)
            kill["trade"] = trade
            kill["tradedPlayer"] = previous_kill["killer"] if trade else None
            kill["tradeSeconds"] = round(kill["seconds"] - previous_kill["seconds"], 1) if trade else None
        for kill in kills_timeline:
            kill.pop("attackerTeamId", None)
            kill.pop("victimTeamId", None)
            kill.pop("_tick", None)
            kill.pop("_victimSteamid", None)

        damage_by_round = []
        damage_by_team = {"HOTU": 0, opponent: 0}
        utility_damage_by_team = {"HOTU": 0, opponent: 0}
        damage_players = defaultdict(lambda: {"dealt": 0, "received": 0, "utility": 0, "hits": 0})
        for event in hurt_by_round.get(i, []):
            attacker_team, victim_team = team_of(event, "attacker"), team_of(event, "user")
            if attacker_team not in (hotu_team_number, opponent_team) or victim_team not in (hotu_team_number, opponent_team):
                continue
            try:
                dealt = max(0, int(event.get("dmg_health") or 0))
                armor_damage = max(0, int(event.get("dmg_armor") or 0))
            except (TypeError, ValueError):
                dealt, armor_damage = 0, 0
            attacker_name, victim_name = safe_text(event.get("attacker_name"), "unknown"), safe_text(event.get("user_name"), "unknown")
            attacker_label = "HOTU" if attacker_team == hotu_team_number else opponent
            victim_label = "HOTU" if victim_team == hotu_team_number else opponent
            damage_by_team[attacker_label] += dealt
            damage_players[attacker_name]["dealt"] += dealt
            damage_players[attacker_name]["hits"] += 1
            damage_players[victim_name]["received"] += dealt
            weapon = safe_text(event.get("weapon"), "unknown").casefold()
            is_utility_damage = any(token in weapon for token in ("hegrenade", "molotov", "incgrenade", "inferno", "firebomb"))
            if is_utility_damage:
                utility_damage_by_team[attacker_label] += dealt
                damage_players[attacker_name]["utility"] += dealt
            damage_by_round.append({"seconds": round(max(0, int(event.get("tick") or 0) - freeze_tick) / 64, 1),
                "attacker": attacker_name, "attackerTeam": attacker_label, "victim": victim_name,
                "victimTeam": victim_label, "damage": dealt, "armorDamage": armor_damage,
                "weapon": safe_text(event.get("weapon"), "unknown"), "hitgroup": safe_text(event.get("hitgroup"), "unknown"),
                "utilityDamage": is_utility_damage})
        damage_players_sorted = [{"name": name, **value} for name, value in sorted(damage_players.items(), key=lambda item: item[1]["dealt"], reverse=True)]
        manpower_advantage_rounds = Counter(k.get("manpowerAdvantage") for k in kills_timeline if k.get("manpowerAdvantage"))
        flash_events = []
        flash_by_team = {"HOTU": {"blinds": 0, "blindSeconds": 0.0, "opponentsBlinded": 0},
                         opponent: {"blinds": 0, "blindSeconds": 0.0, "opponentsBlinded": 0, "blindSecondsOnHOTU": 0.0}}
        flash_players = defaultdict(lambda: {"blinds": 0, "blindSeconds": 0.0, "opponentsBlinded": 0})
        for event in blind_by_round.get(i, []):
            attacker_team, victim_team = team_of(event, "attacker"), team_of(event, "user")
            if attacker_team not in (hotu_team_number, opponent_team) or victim_team not in (hotu_team_number, opponent_team):
                continue
            attacker_name, victim_name = safe_text(event.get("attacker_name"), "unknown"), safe_text(event.get("user_name"), "unknown")
            attacker_label = "HOTU" if attacker_team == hotu_team_number else opponent
            victim_label = "HOTU" if victim_team == hotu_team_number else opponent
            try:
                duration = max(0.0, float(event.get("blind_duration") or 0))
            except (TypeError, ValueError):
                duration = 0.0
            flash_by_team[attacker_label]["blinds"] += 1
            flash_by_team[attacker_label]["blindSeconds"] += duration
            flash_players[attacker_name]["blinds"] += 1
            flash_players[attacker_name]["blindSeconds"] += duration
            if attacker_team != victim_team:
                flash_by_team[attacker_label]["opponentsBlinded"] += 1
                flash_players[attacker_name]["opponentsBlinded"] += 1
                if attacker_team == opponent_team and victim_team == hotu_team_number:
                    flash_by_team[attacker_label]["blindSecondsOnHOTU"] += duration
            flash_events.append({"seconds": round(max(0, int(event.get("tick") or 0) - freeze_tick) / 64, 1),
                "attacker": attacker_name, "attackerTeam": attacker_label, "victim": victim_name,
                "victimTeam": victim_label, "duration": round(duration, 2),
                "blindedOpponent": attacker_team != victim_team})
        for data in flash_by_team.values():
            data["blindSeconds"] = round(data["blindSeconds"], 1)
            if "blindSecondsOnHOTU" in data:
                data["blindSecondsOnHOTU"] = round(data["blindSecondsOnHOTU"], 1)
        flash_players_sorted = [{"name": name, **{**data, "blindSeconds": round(data["blindSeconds"], 1)}}
                                for name, data in sorted(flash_players.items(), key=lambda item: item[1]["opponentsBlinded"], reverse=True)]

        plant = next((event for event in plant_by_round.get(i, []) if team_of(event, "user") in (hotu_team_number, opponent_team)), None)
        plant_site_raw = safe_text(plant.get("user_CCSPlayerPawn.m_szLastPlaceName")) if plant else ""
        plant_site = "A" if "bombsitea" in plant_site_raw.casefold() else "B" if "bombsiteb" in plant_site_raw.casefold() else None
        plant_time = round((int(plant.get("tick") or 0) - freeze_tick) / 64, 1) if plant else None
        attacking_team = hotu_team_number if hotu_side == "T" else opponent_team
        attack_name = "HOTU" if attacking_team == hotu_team_number else opponent
        round_nades = []
        for _event_name, key, label in utility_names:
            for event in utility_round_events[key].get(i, []):
                team = team_of(event, "user")
                if team not in (hotu_team_number, opponent_team):
                    continue
                x, y = event.get("x"), event.get("y")
                site, distance = nearest_site(x, y)
                round_nades.append({"type": label, "team": "HOTU" if team == hotu_team_number else opponent,
                                    "player": safe_text(event.get("user_name"), "unknown"),
                                    "seconds": round(max(0, int(event.get("tick") or 0) - freeze_tick) / 64, 1),
                                    "throwerLocation": safe_text(event.get("user_CCSPlayerPawn.m_szLastPlaceName"), "Unknown"),
                                    "siteArea": site, "x": round(float(x), 1) if x is not None else None,
                                    "y": round(float(y), 1) if y is not None else None})
        round_nades.sort(key=lambda event: event["seconds"])
        plant_nades = [n for n in round_nades if n["team"] == attack_name and plant_time is not None and plant_time - 25 <= n["seconds"] <= plant_time]
        utility_at_site = sorted({n["type"] for n in plant_nades if n["siteArea"] == plant_site}) if plant_site else []
        opposite_nades = [n for n in plant_nades if plant_site and n["siteArea"] and n["siteArea"] != plant_site]
        fake_candidate = None
        if plant_site and len(opposite_nades) >= 2 and len({n["type"] for n in opposite_nades}) >= 2:
            fake_candidate = {"status": "hypothesis", "utilityCount": len(opposite_nades), "utilityTypes": sorted({n["type"] for n in opposite_nades}),
                              "oppositeSite": opposite_nades[0]["siteArea"], "plantSite": plant_site,
                              "text": "Возможная ложная угроза до выхода на другую точку; проверить звук, движение и реакцию защиты по видео."}
        execute_candidate = {"status": "hypothesis", "site": plant_site, "utilityTypes": utility_at_site,
                             "text": "Раунд с plant и utility у точки; это кандидат на выход с раскидом, не подтверждение заранее заготовленного execute."} if plant_site and len(utility_at_site) >= 2 else None

        defenders = []
        for state in contact_states:
            team = state_team(state)
            if team != (opponent_team if attacking_team == hotu_team_number else hotu_team_number):
                continue
            site, distance = nearest_site(state.get("X"), state.get("Y"))
            defenders.append({"name": safe_text(state.get("name"), "игрок"), "location": safe_text(state.get("last_place_name"), "Unknown"),
                              "nearestSite": site, "distance": distance})
        stack_counts = {site: sum(row["nearestSite"] == site and (row["distance"] or 99999) <= 1000 for row in defenders) for site in ("A", "B")}
        stacked_site = max(stack_counts, key=stack_counts.get) if stack_counts else None
        if stacked_site and stack_counts[stacked_site] < 3:
            stacked_site = None
        contact_offset = round(max(0, contact_tick - freeze_tick) / 64, 1)
        spacing_rows = defaultdict(list)
        for state in contact_states:
            team = state_team(state)
            if team not in (hotu_team_number, opponent_team):
                continue
            try:
                x, y = float(state.get("X")), float(state.get("Y"))
                if math.isfinite(x) and math.isfinite(y):
                    spacing_rows[team].append((safe_text(state.get("name"), "игрок"),
                                               safe_text(state.get("last_place_name"), "Unknown"), x, y))
            except (TypeError, ValueError):
                continue
        spacing_snapshot = {}
        for team_number, team_name in ((hotu_team_number, "HOTU"), (opponent_team, opponent)):
            rows_for_team = spacing_rows.get(team_number, [])
            player_spacing = []
            for name, location, x, y in rows_for_team:
                mates = [(other_name, math.hypot(x - ox, y - oy)) for other_name, _other_loc, ox, oy in rows_for_team if other_name != name]
                if mates:
                    nearest_name, nearest_distance = min(mates, key=lambda row: row[1])
                    player_spacing.append({"name": name, "location": location, "nearestMate": nearest_name,
                                           "distance": round(nearest_distance), "isolated": nearest_distance >= 1400})
            spacing_snapshot[team_name] = {
                "players": player_spacing,
                "averageNearestDistance": round(sum(p["distance"] for p in player_spacing) / len(player_spacing)) if player_spacing else None,
                "isolatedPlayers": [p["name"] for p in player_spacing if p["isolated"]],
            }

        round_review.append({
            "round": i, "side": hotu_side, "winner": winner,
            "buy": {"HOTU": loadouts["HOTU"], opponent: loadouts[opponent]},
            "firstKill": ({"killer": rr["first"][2], "killerTeam": "HOTU" if rr["first"][0] == hotu_team_number else opponent,
                           "victim": rr["first"][3], "victimLocation": rr["first"][1],
                           "seconds": round(max(0, rr["first"][4] - freeze_tick) / 64, 1)} if rr["first"] else None),
            "plant": {"team": "HOTU" if team_of(plant, "user") == hotu_team_number else opponent, "site": plant_site, "seconds": plant_time,
                      "player": safe_text(plant.get("user_name"), "unknown")} if plant else None,
            "defuse": bool(defuse_by_round.get(i)),
            "defusePlayer": ({"player": safe_text(defuse_by_round[i][0].get("user_name"), "unknown"),
                              "team": "HOTU" if team_of(defuse_by_round[i][0], "user") == hotu_team_number else opponent,
                              "seconds": round(max(0, int(defuse_by_round[i][0].get("tick") or 0) - freeze_tick) / 64, 1)}
                             if defuse_by_round.get(i) else None),
            "kills": kills_timeline,
            "damage": {"events": damage_by_round, "teams": damage_by_team, "utilityTeams": utility_damage_by_team,
                       "players": damage_players_sorted,
                       "blindEventsAvailable": bool(blind_events)},
            "flash": {"available": bool(blind_events), "events": flash_events,
                      "teams": flash_by_team, "opponentBlindSecondsOnHOTU": flash_by_team.get(opponent, {}).get("blindSecondsOnHOTU", 0),
                      "players": flash_players_sorted},
            "manpower": {"trackedDeaths": len(manpower), "advantageAfterKills": dict(manpower_advantage_rounds),
                         "finalHotuAlive": alive[hotu_team_number], "finalOpponentAlive": alive[opponent_team],
                         "swings": [k["advantageSwing"] for k in kills_timeline if k.get("advantageSwing")]},
            "trades": sum(k["trade"] for k in kills_timeline), "utility": round_nades,
            "executionCandidate": execute_candidate, "fakeCandidate": fake_candidate,
            "defenseSnapshot": {"secondsBeforeContact": 5, "capturedAt": contact_offset, "players": defenders,
                                "nearA": stack_counts.get("A", 0), "nearB": stack_counts.get("B", 0),
                                "stackCandidate": stacked_site},
            "spacingSnapshot": {"capturedAt": contact_offset, "isolatedThreshold": 1400, "teams": spacing_snapshot},
        })

    team_economy = {team: {buy: values for buy, values in sorted(summary.items())} for team, summary in team_economy.items()}

    # The next round's pre-buy wallet is the observed result of win/loss rewards,
    # kill and objective bonuses, loss-bonus progression, and retained equipment.
    for index, current in enumerate(round_review):
        next_round = round_review[index + 1] if index + 1 < len(round_review) else None
        if not next_round:
            continue
        for team_name in ("HOTU", opponent):
            upcoming = next_round["buy"].get(team_name, {})
            current_buy = current["buy"].get(team_name, {})
            current_buy["nextRoundEconomy"] = {
                "round": next_round["round"],
                "cashBeforePurchase": upcoming.get("cashBeforePurchase"),
                "cashPlayers": upcoming.get("cashPlayers"),
                "players": upcoming.get("players"),
                "purchaseSpend": upcoming.get("purchaseSpend"),
                "buyType": upcoming.get("buyType"),
            }
            assessment = current_buy.get("economyAssessment")
            if assessment and upcoming.get("cashBeforePurchase") is not None:
                assessment["nextRoundDetail"] = (
                    f"Следующий раунд: перед закупом у команды было ${upcoming['cashBeforePurchase']:,}; "
                    f"фактический класс закупа — {upcoming.get('buyType', 'нет данных')}, "
                    f"потрачено ${upcoming.get('purchaseSpend'):,}."
                    if upcoming.get("purchaseSpend") is not None else
                    f"Следующий раунд: перед закупом у команды было ${upcoming['cashBeforePurchase']:,}; "
                    f"класс закупа — {upcoming.get('buyType', 'нет данных')}."
                )

    return {
        "name": map_name, "score": ordered(score), "pick": "Пик не определяется демо", "teamDetection": team_detection,
        "halves": halves, "sideNames": half_side, "kills": ordered(kills),
        "plants": ordered(plants_count), "plantWins": ordered(plant_wins),
        "openers": ordered(openers), "openWins": ordered(open_wins),
        "zones": [[name, count] for name, count in zones.most_common(8)],
        "opponentPatterns": opponent_patterns,
        "pistolRounds": pistol_analysis,
        "roundReview": round_review, "teamEconomy": team_economy,
        "grenadeTracks": grenade_tracks,
        "playerTracks": [{"steamid": sid, "name": player_names.get(sid, "Игрок"),
                          "team": "HOTU" if player_team.get(sid) == hotu_team_number else opponent,
                          "points": sorted(points, key=lambda point: (point["round"], point["seconds"]))}
                         for sid, points in player_tracks.items() if points],
        "trajectorySampleSeconds": 5,
        "utility": utility,
        "topHotu": [[name, count] for name, count in player_kills.most_common() if name in player_names.values() and player_team.get(next((sid for sid, nm in player_names.items() if nm == name), "")) == hotu_team_number][:5],
        "firstHalfScore": f"{halves[0][0]}:{halves[0][1]}",
        "secondHalfScore": f"{halves[1][0]}:{halves[1][1]}",
        "keyRounds": [], "rounds": len(round_stats),
    }


def persist_reports(opponent: str, source_url: str, maps: list[dict]):
    """Keep parsed reports (never raw demos) for cross-match scouting trends."""
    now = datetime.now(timezone.utc).isoformat(timespec="seconds")
    opponent_key = opponent.casefold().strip()
    source_key = source_url.strip() or f"local-upload-{now}"
    with sqlite3.connect(DB_PATH) as db:
        db.execute("""CREATE TABLE IF NOT EXISTS map_reports (
            opponent_key TEXT NOT NULL, opponent TEXT NOT NULL, source_url TEXT NOT NULL,
            map_name TEXT NOT NULL, report_json TEXT NOT NULL, updated_at TEXT NOT NULL,
            PRIMARY KEY(opponent_key, source_url, map_name))""")
        for report in maps:
            db.execute("""INSERT INTO map_reports VALUES (?, ?, ?, ?, ?, ?)
                ON CONFLICT(opponent_key, source_url, map_name) DO UPDATE SET
                opponent=excluded.opponent, report_json=excluded.report_json, updated_at=excluded.updated_at""",
                (opponent_key, opponent, source_key, report["name"], json.dumps(report, ensure_ascii=False), now))
        db.commit()
    return source_key


def history_for(opponent: str, map_name: str):
    """Aggregate evidence over distinct uploaded match pages for one opponent/map."""
    if not DB_PATH.exists():
        return None
    opponent_key = opponent.casefold().strip()
    with sqlite3.connect(DB_PATH) as db:
        rows_db = db.execute("SELECT source_url, report_json FROM map_reports WHERE opponent_key=? AND map_name=?",
                             (opponent_key, map_name)).fetchall()
        hotu_rows_db = db.execute("SELECT source_url, report_json FROM map_reports WHERE map_name=?",
                                  (map_name,)).fetchall()
    reports = [(source, json.loads(payload)) for source, payload in rows_db]
    trend_reports = {(source, map_name): report for source, report in reports}
    for source, payload in hotu_rows_db:
        if (source, map_name) in trend_reports:
            continue
        report = json.loads(payload)
        if any(track.get("team") == "HOTU" for track in report.get("playerTracks", [])):
            trend_reports[(source, map_name)] = report
    if not reports:
        return None
    result = {"matches": len({source for source, _ in reports}), "demos": len(reports),
              "attackRounds": 0, "attackWins": 0, "openingRounds": 0, "openingWins": 0,
              "plantSites": {}, "nades": {}, "entryPlayers": {}, "hotuFirstVictims": {},
              "pistolRounds": {"count": 0, "wins": 0, "sideWins": {"CT": 0, "T": 0}, "nextRoundWins": 0, "wonPistolsWithNext": 0},
              "defense": {"rounds": 0, "wins": 0, "openingRounds": 0, "openingWins": 0,
                          "plantsAllowed": 0, "hotuWinsAfterPlant": 0, "plantSitesAllowed": {}, "nades": {}, "entryPlayers": {}}}

    def add_nades(target, items):
        for nade in items or []:
            row = target.setdefault(nade["type"], {"count": 0, "earlyCount": 0, "spots": {}})
            row["count"] += int(nade.get("count", 0))
            row["earlyCount"] += int(nade.get("earlyCount", 0))
            for spot in nade.get("commonSpots", []):
                key = (int(spot["x"]), int(spot["y"]))
                val = row["spots"].setdefault(key, {"rounds": 0, "events": 0})
                val["rounds"] += int(spot.get("rounds", 0))
                val["events"] += int(spot.get("events", 0))

    def add_players(target, items, name_key, count_key):
        for item in items or []:
            name = item[name_key]
            row = target.setdefault(name, {count_key: 0, "wins": 0})
            row[count_key] += int(item.get(count_key, 0))
            row["wins"] += int(item.get("wins", 0))

    for _source, report in reports:
        pistols = report.get("pistolRounds", {})
        result["pistolRounds"]["count"] += int(pistols.get("count", 0))
        result["pistolRounds"]["wins"] += int(pistols.get("wins", 0))
        for side in ("CT", "T"):
            result["pistolRounds"]["sideWins"][side] += int(pistols.get("sideWins", {}).get(side, 0))
        pistol_rows = pistols.get("rounds", [])
        for pistol in pistol_rows:
            if pistol.get("winner") == "HOTU":
                result["pistolRounds"]["wonPistolsWithNext"] += 1
                if pistol.get("nextRoundWinner") == "HOTU":
                    result["pistolRounds"]["nextRoundWins"] += 1
        p = report.get("opponentPatterns", {})
        for key in ("attackRounds", "attackWins", "openingRounds", "openingWins"):
            result[key] += int(p.get(key, 0))
        for site in p.get("plantSites", []):
            row = result["plantSites"].setdefault(site["site"], {"plants": 0, "wins": 0})
            row["plants"] += int(site.get("plants", 0)); row["wins"] += int(site.get("wins", 0))
        add_nades(result["nades"], p.get("nades"))
        add_players(result["entryPlayers"], p.get("entryPlayers"), "name", "openings")
        for name, count in p.get("hotuFirstVictims", []):
            result["hotuFirstVictims"][name] = result["hotuFirstVictims"].get(name, 0) + int(count)
        d = p.get("defense", {})
        for key in ("rounds", "wins", "openingRounds", "openingWins", "plantsAllowed", "hotuWinsAfterPlant"):
            result["defense"][key] += int(d.get(key, 0))
        for site in d.get("plantSitesAllowed", []):
            row = result["defense"]["plantSitesAllowed"].setdefault(site["site"], {"plants": 0, "hotuWins": 0})
            row["plants"] += int(site.get("plants", 0)); row["hotuWins"] += int(site.get("hotuWins", 0))
        add_nades(result["defense"]["nades"], d.get("nades"))
        add_players(result["defense"]["entryPlayers"], d.get("entryPlayers"), "name", "openings")

    def finish_nades(source, denominator_key):
        out = []
        denominator = result.get(denominator_key, 0) if denominator_key in result else result["defense"].get(denominator_key, 0)
        for name, row in source.items():
            spots = [{"x": xy[0], "y": xy[1], **vals} for xy, vals in row["spots"].items()]
            spots.sort(key=lambda s: (s["rounds"], s["events"]), reverse=True)
            out.append({"type": name, "count": row["count"], "earlyCount": row["earlyCount"],
                        "perRound": round(row["count"] / denominator, 2) if denominator else 0,
                        "commonSpots": spots[:3]})
        return out

    result["plantSites"] = [{"site": k, **v} for k, v in result["plantSites"].items()]
    result["entryPlayers"] = [{"name": k, **v} for k, v in sorted(result["entryPlayers"].items(), key=lambda x: x[1]["openings"], reverse=True)[:5]]
    result["hotuFirstVictims"] = sorted([[k, v] for k, v in result["hotuFirstVictims"].items()], key=lambda x: x[1], reverse=True)[:5]
    result["nades"] = finish_nades(result["nades"], "attackRounds")
    defense = result["defense"]
    defense["plantSitesAllowed"] = [{"site": k, **v} for k, v in defense["plantSitesAllowed"].items()]
    defense["entryPlayers"] = [{"name": k, **v} for k, v in sorted(defense["entryPlayers"].items(), key=lambda x: x[1]["openings"], reverse=True)[:5]]
    defense["nades"] = finish_nades(defense["nades"], "rounds")
    player_side_trends = {}
    utility_labels = {"Дым", "Флешка", "HE", "Молотов", "Incendiary"}
    for (source, _map_name), report in trend_reports.items():
        rounds_by_number = {int(r.get("round") or 0): r for r in report.get("roundReview", [])}
        for track in report.get("playerTracks", []):
            name = safe_text(track.get("name"), "Игрок")
            is_hotu = track.get("team") == "HOTU"
            team_label = "HOTU" if is_hotu else "соперник"
            player_events = defaultdict(lambda: {"rounds": set(), "positionSamples": 0, "areas": Counter(),
                                                  "firstKills": 0, "firstDeaths": 0, "kills": 0,
                                                  "deaths": 0, "nades": 0, "plants": 0, "matches": set()})
            for round_report in report.get("roundReview", []):
                side = round_report.get("side")
                if not is_hotu and side in ("CT", "T"):
                    side = "T" if side == "CT" else "CT"
                row = player_events[side]
                row["matches"].add(source)
                row["rounds"].add((source, round_report.get("round")))
                opening = round_report.get("firstKill") or {}
                if opening.get("killer") == name:
                    row["firstKills"] += 1
                if opening.get("victim") == name:
                    row["firstDeaths"] += 1
                for kill in round_report.get("kills", []):
                    if kill.get("killer") == name:
                        row["kills"] += 1
                    if kill.get("victim") == name:
                        row["deaths"] += 1
                row["nades"] += sum(nade.get("player") == name and nade.get("type") in utility_labels
                                    for nade in round_report.get("utility", []))
                plant = round_report.get("plant") or {}
                if plant.get("player") == name and plant.get("team") == track.get("team"):
                    row["plants"] += 1
            for point in track.get("points", []):
                round_report = rounds_by_number.get(int(point.get("round") or 0), {})
                side = round_report.get("side")
                if not is_hotu and side in ("CT", "T"):
                    side = "T" if side == "CT" else "CT"
                row = player_events[side]
                row["positionSamples"] += 1
                area = safe_text(point.get("area"), "").strip()
                if area and area.lower() != "unknown":
                    row["areas"][area] += 1
            for side, values in player_events.items():
                key = (team_label, name, side)
                out = player_side_trends.setdefault(key, {"team": team_label, "name": name, "side": side,
                    "matches": set(), "rounds": set(), "positionSamples": 0, "areas": Counter(),
                    "firstKills": 0, "firstDeaths": 0, "kills": 0, "deaths": 0, "nades": 0, "plants": 0})
                out["matches"].update(values["matches"])
                out["rounds"].update(values["rounds"])
                out["positionSamples"] += values["positionSamples"]
                out["areas"].update(values["areas"])
                for metric in ("firstKills", "firstDeaths", "kills", "deaths", "nades", "plants"):
                    out[metric] += values[metric]
    result["playerSideTrends"] = []
    for key in sorted(player_side_trends):
        row = player_side_trends[key]
        result["playerSideTrends"].append({"team": row["team"], "name": row["name"], "side": row["side"],
            "matches": len(row["matches"]), "rounds": len(row["rounds"]), "positionSamples": row["positionSamples"],
            "firstKills": row["firstKills"], "firstDeaths": row["firstDeaths"], "kills": row["kills"],
            "deaths": row["deaths"], "nades": row["nades"], "plants": row["plants"],
            "topAreas": [{"area": area, "samples": count} for area, count in row["areas"].most_common(4)]})
    return result


def saved_matches():
    """Return saved match cards without sending full round timelines."""
    if not DB_PATH.exists():
        return []
    with sqlite3.connect(DB_PATH) as db:
        rows_db = db.execute(
            "SELECT opponent, source_url, map_name, report_json, updated_at FROM map_reports ORDER BY updated_at DESC, rowid ASC"
        ).fetchall()
    grouped = {}
    for opponent, source_url, map_name, payload, updated_at in rows_db:
        key = (opponent.casefold(), source_url)
        match = grouped.setdefault(key, {"opponent": opponent, "sourceUrl": source_url,
                                         "updatedAt": updated_at, "maps": []})
        report = json.loads(payload)
        match["maps"].append({"name": map_name, "score": report.get("score", [0, 0]),
                              "rounds": report.get("rounds", 0)})
        if updated_at > match["updatedAt"]:
            match["updatedAt"] = updated_at
    result = list(grouped.values())
    for match in result:
        match["series"] = [sum(m["score"][0] > m["score"][1] for m in match["maps"]),
                           sum(m["score"][0] < m["score"][1] for m in match["maps"])]
    result.sort(key=lambda item: item["updatedAt"], reverse=True)
    return result


def opponent_profiles():
    """Summarize each opponent across all saved matches and maps."""
    if not DB_PATH.exists():
        return []
    with sqlite3.connect(DB_PATH) as db:
        rows_db = db.execute(
            "SELECT opponent, source_url, map_name, report_json FROM map_reports ORDER BY updated_at DESC"
        ).fetchall()
    def empty_pistols():
        return {"rounds": 0, "hotuWins": 0, "opponentWins": 0,
                "bySide": {side: {"rounds": 0, "hotuWins": 0} for side in ("CT", "T")},
                "hotuNextAttempts": 0, "hotuNextWins": 0,
                "opponentNextAttempts": 0, "opponentNextWins": 0}

    def add_pistols(target, pistol_report):
        for pistol in pistol_report.get("rounds", []):
            side = pistol.get("hotuSide")
            winner = pistol.get("winner")
            target["rounds"] += 1
            if side in target["bySide"]:
                target["bySide"][side]["rounds"] += 1
            if winner == "HOTU":
                target["hotuWins"] += 1
                if side in target["bySide"]:
                    target["bySide"][side]["hotuWins"] += 1
                if pistol.get("nextRoundWinner") is not None:
                    target["hotuNextAttempts"] += 1
                    target["hotuNextWins"] += int(pistol.get("nextRoundWinner") == "HOTU")
            elif winner:
                target["opponentWins"] += 1
                if pistol.get("nextRoundWinner") is not None:
                    target["opponentNextAttempts"] += 1
                    target["opponentNextWins"] += int(pistol.get("nextRoundWinner") != "HOTU")

    profiles = {}
    for opponent, source, map_name, payload in rows_db:
        profile = profiles.setdefault(opponent.casefold(), {
            "name": opponent, "sources": set(), "maps": {}, "pistols": empty_pistols()
        })
        profile["sources"].add(source)
        report = json.loads(payload)
        bucket = profile["maps"].setdefault(map_name, {
            "name": map_name, "sources": set(), "demos": 0, "hotuWins": 0,
            "opponentWins": 0, "rounds": 0, "hotuRounds": 0, "opponentRounds": 0,
            "attackRounds": 0, "attackWins": 0, "openingRounds": 0, "openingWins": 0,
            "plants": {}, "entries": {}, "ctRounds": 0, "ctWins": 0,
            "ctOpeningRounds": 0, "ctOpeningWins": 0, "plantsAllowed": 0, "hotuWinsAfterPlant": 0, "defenseEntries": {}, "pistols": empty_pistols(),
            "damageHealth": 0, "damageToHotu": 0, "utilityHealthDamage": 0, "damagePlayers": {},
            "flashBlinds": 0, "flashBlindSeconds": 0.0, "flashBlindSecondsOnHotu": 0.0, "opponentsBlinded": 0, "flashDataMaps": 0, "flashPlayers": {},
        })
        bucket["sources"].add(source)
        bucket["demos"] += 1
        score = report.get("score") or [0, 0]
        if len(score) >= 2:
            bucket["hotuRounds"] += int(score[0] or 0)
            bucket["opponentRounds"] += int(score[1] or 0)
            bucket["rounds"] += int(score[0] or 0) + int(score[1] or 0)
            bucket["hotuWins"] += int(score[0] > score[1])
            bucket["opponentWins"] += int(score[1] > score[0])
        pistol_report = report.get("pistolRounds") or {}
        add_pistols(profile["pistols"], pistol_report)
        add_pistols(bucket["pistols"], pistol_report)
        patterns = report.get("opponentPatterns") or {}
        damage = patterns.get("damage") or {}
        bucket["damageHealth"] += int(damage.get("healthDamage", 0) or 0)
        bucket["damageToHotu"] += int(damage.get("damageToHOTU", 0) or 0)
        bucket["utilityHealthDamage"] += int(damage.get("utilityHealthDamage", 0) or 0)
        for item in damage.get("players", []):
            player = bucket["damagePlayers"].setdefault(safe_text(item.get("name"), "Unknown"),
                {"healthDamage": 0, "utilityDamage": 0, "hits": 0})
            player["healthDamage"] += int(item.get("healthDamage", 0) or 0)
            player["utilityDamage"] += int(item.get("utilityDamage", 0) or 0)
            player["hits"] += int(item.get("hits", 0) or 0)
        flash = damage.get("flash") or {}
        bucket["flashDataMaps"] += int(bool(damage.get("flashBlindnessAvailable")))
        bucket["flashBlinds"] += int(flash.get("blinds", 0) or 0)
        bucket["flashBlindSeconds"] += float(flash.get("blindSeconds", 0) or 0)
        bucket["flashBlindSecondsOnHotu"] += float(flash.get("blindSecondsOnHOTU", 0) or 0)
        bucket["opponentsBlinded"] += int(flash.get("opponentsBlinded", 0) or 0)
        for item in flash.get("players", []):
            player = bucket["flashPlayers"].setdefault(safe_text(item.get("name"), "Unknown"),
                {"blinds": 0, "blindSeconds": 0.0, "opponentsBlinded": 0})
            player["blinds"] += int(item.get("blinds", 0) or 0)
            player["blindSeconds"] += float(item.get("blindSeconds", 0) or 0)
            player["opponentsBlinded"] += int(item.get("opponentsBlinded", 0) or 0)
        for key in ("attackRounds", "attackWins", "openingRounds", "openingWins"):
            bucket[key] += int(patterns.get(key, 0) or 0)
        for item in patterns.get("plantSites", []):
            site = str(item.get("site") or "unknown")
            value = bucket["plants"].setdefault(site, {"plants": 0, "wins": 0})
            value["plants"] += int(item.get("plants", 0) or 0)
            value["wins"] += int(item.get("wins", 0) or 0)
        for item in patterns.get("entryPlayers", []):
            name = safe_text(item.get("name"), "Unknown")
            value = bucket["entries"].setdefault(name, {"openings": 0, "wins": 0})
            value["openings"] += int(item.get("openings", 0) or 0)
            value["wins"] += int(item.get("wins", 0) or 0)
        defense = patterns.get("defense") or {}
        bucket["ctRounds"] += int(defense.get("rounds", 0) or 0)
        bucket["ctWins"] += int(defense.get("wins", 0) or 0)
        bucket["ctOpeningRounds"] += int(defense.get("openingRounds", 0) or 0)
        bucket["ctOpeningWins"] += int(defense.get("openingWins", 0) or 0)
        bucket["plantsAllowed"] += int(defense.get("plantsAllowed", 0) or 0)
        bucket["hotuWinsAfterPlant"] += int(defense.get("hotuWinsAfterPlant", 0) or 0)
        for item in defense.get("entryPlayers", []):
            name = safe_text(item.get("name"), "Unknown")
            value = bucket["defenseEntries"].setdefault(name, {"openings": 0, "wins": 0})
            value["openings"] += int(item.get("openings", 0) or 0)
            value["wins"] += int(item.get("wins", 0) or 0)
    result = []
    for profile in profiles.values():
        maps = []
        for bucket in profile["maps"].values():
            opening_rounds = bucket["openingRounds"]
            attack_rounds = bucket["attackRounds"]
            defense_rounds = bucket["ctRounds"]
            total_plants = sum(item["plants"] for item in bucket["plants"].values())
            total_entry_kills = sum(item["openings"] for item in bucket["entries"].values())
            confidence = ("высокая" if bucket["demos"] >= 5 and bucket["rounds"] >= 100 else
                          "средняя" if bucket["demos"] >= 3 and bucket["rounds"] >= 60 else "предварительная")
            insights = []
            if attack_rounds >= 6:
                attack_rate = bucket["attackWins"] / attack_rounds
                if attack_rate >= 0.60:
                    insights.append({"type": "attack", "title": "Сильная атака соперника",
                        "evidence": f"{bucket['attackWins']}/{attack_rounds} T-раундов выиграны ({round(attack_rate * 100)}%).",
                        "action": "На CT заранее распределить утилити на ранний контроль ключевых зон и держать план ротации после подтверждения выхода."})
                elif attack_rate <= 0.40:
                    insights.append({"type": "attack", "title": "Атаку соперника удавалось сдерживать",
                        "evidence": f"{bucket['attackWins']}/{attack_rounds} T-раундов выиграны ({round(attack_rate * 100)}%).",
                        "action": "Сохранить рабочую структуру защиты; проверить, какие позиции и тайминги дали результат, и не отдавать бесплатную раннюю информацию."})
            if defense_rounds >= 6:
                defense_rate = bucket["ctWins"] / defense_rounds
                if defense_rate >= 0.60:
                    insights.append({"type": "defense", "title": "Сильная защита соперника за CT",
                        "evidence": f"{bucket['ctWins']}/{defense_rounds} защитных раундов выиграны ({round(defense_rate * 100)}%).",
                        "action": "На T готовить выход с несколькими стадиями utility и планом на смену точки; не превращать первый контакт в одиночный вход против подготовленной защиты."})
                elif defense_rate <= 0.40:
                    insights.append({"type": "defense", "title": "Защиту соперника за CT удавалось вскрывать",
                        "evidence": f"{bucket['ctWins']}/{defense_rounds} защитных раундов выиграны ({round(defense_rate * 100)}%).",
                        "action": "Сверить удачные T-раунды HOTU и закрепить их базовые условия: ранний контроль, своевременный трейд и безопасный выход на plant."})
            if opening_rounds >= 5:
                opening_rate = bucket["openingWins"] / opening_rounds
                if opening_rate >= 0.65:
                    insights.append({"type": "opening", "title": "Соперник хорошо конвертирует первый фраг",
                        "evidence": f"{bucket['openingWins']}/{opening_rounds} раундов выиграны после первого убийства соперника ({round(opening_rate * 100)}%).",
                        "action": "Приоритет — не допускать изолированных первых дуэлей; заранее назначить разменную позицию и после потери игрока быстро стабилизировать состав."})
                elif opening_rate <= 0.40:
                    insights.append({"type": "opening", "title": "Первое убийство не всегда приносило сопернику раунд",
                        "evidence": f"{bucket['openingWins']}/{opening_rounds} раундов выиграны после первого убийства соперника ({round(opening_rate * 100)}%).",
                        "action": "Если соперник забрал entry, проверить возможность сыграть на перегруппировку и поздний повторный контакт, а не отдавать пространство автоматически."})
            if total_plants >= 4:
                most_planted = max(bucket["plants"].items(), key=lambda item: item[1]["plants"])
                site, site_data = most_planted
                share = site_data["plants"] / total_plants
                if share >= 0.60:
                    insights.append({"type": "site", "title": f"Смещение plant на {site}",
                        "evidence": f"{site_data['plants']}/{total_plants} plant ({round(share * 100)}%) пришлись на {site}.",
                        "action": f"Подготовить отдельный сценарий защиты {site}: стартовые позиции, тайминг ротации и сохранение гранат для остановки выхода."})
            if total_entry_kills >= 3 and opening_rounds:
                entry_name, entry_data = max(bucket["entries"].items(), key=lambda item: item[1]["openings"])
                entry_share = entry_data["openings"] / opening_rounds
                if entry_share >= 0.35:
                    insights.append({"type": "player", "title": f"Частый entry-игрок: {entry_name}",
                        "evidence": f"{entry_data['openings']} из {opening_rounds} первых убийств соперника ({round(entry_share * 100)}%).",
                        "action": "Разобрать его повторяемые стартовые маршруты и подготовить парную помощь/контргранату на этих направлениях."})
            if bucket["plantsAllowed"] >= 5:
                post_plant_rate = bucket["hotuWinsAfterPlant"] / bucket["plantsAllowed"]
                if post_plant_rate >= 0.70:
                    insights.append({"type": "postplant", "title": "HOTU часто конвертировала plant против их CT",
                        "evidence": f"{bucket['hotuWinsAfterPlant']}/{bucket['plantsAllowed']} раундов с plant HOTU выиграны.",
                        "action": "Сохранить успешную пост-плэнт дисциплину на этой карте: разменные позиции, контроль defuse-линий и распределение оставшейся utility."})
                elif post_plant_rate <= 0.40:
                    insights.append({"type": "postplant", "title": "Низкая конверсия HOTU после plant против их CT",
                        "evidence": f"{bucket['hotuWinsAfterPlant']}/{bucket['plantsAllowed']} раундов с plant HOTU выиграны.",
                        "action": "Разобрать решения после установки отдельно от выхода: позиции на размен, контроль бомбы и момент начала ретейка."})
            defense_entry_total = bucket["ctOpeningRounds"]
            if defense_entry_total >= 3:
                defender_name, defender_data = max(bucket["defenseEntries"].items(), key=lambda item: item[1]["openings"])
                defender_share = defender_data["openings"] / defense_entry_total
                if defender_share >= 0.40:
                    insights.append({"type": "ct_player", "title": f"Частый CT-entry игрок: {defender_name}",
                        "evidence": f"{defender_data['openings']} из {defense_entry_total} первых убийств соперника за CT ({round(defender_share * 100)}%).",
                        "action": "В T-разборе проверить его ранние пики и позиции; подготовить безопасную проверку зоны через utility или разменную пару."})
            confidence_note = confidence
            maps.append({**{k: v for k, v in bucket.items() if k not in ("sources", "plants", "entries", "defenseEntries")},
                "matches": len(bucket["sources"]),
                "insights": insights, "insightConfidence": confidence_note,
                "plants": [{"site": site, **value} for site, value in sorted(bucket["plants"].items(), key=lambda pair: pair[1]["plants"], reverse=True)],
                "entries": [{"name": name, **value} for name, value in sorted(bucket["entries"].items(), key=lambda pair: pair[1]["openings"], reverse=True)[:5]],
                "defenseEntries": [{"name": name, **value} for name, value in sorted(bucket["defenseEntries"].items(), key=lambda pair: pair[1]["openings"], reverse=True)[:5]],
                "damagePlayers": [{"name": name, **value} for name, value in sorted(bucket["damagePlayers"].items(), key=lambda pair: pair[1]["healthDamage"], reverse=True)[:5]],
                "flashPlayers": [{"name": name, **value} for name, value in sorted(bucket["flashPlayers"].items(), key=lambda pair: pair[1]["opponentsBlinded"], reverse=True)[:5]],
            })
        maps.sort(key=lambda item: (-item["matches"], -item["demos"], item["name"]))
        result.append({"name": profile["name"], "matches": len(profile["sources"]),
                       "maps": maps, "pistols": profile["pistols"]})
    result.sort(key=lambda item: item["name"].casefold())
    return result


def load_saved_match(source_url: str):
    """Load one saved match with current cross-match opponent patterns."""
    if not DB_PATH.exists():
        return None
    with sqlite3.connect(DB_PATH) as db:
        rows_db = db.execute(
            "SELECT opponent, map_name, report_json FROM map_reports WHERE source_url=? ORDER BY rowid",
            (source_url,),
        ).fetchall()
    if not rows_db:
        return None
    opponent = rows_db[0][0]
    maps = []
    for _, map_name, payload in rows_db:
        report = json.loads(payload)
        report["historyPatterns"] = history_for(opponent, map_name)
        maps.append(report)
    return {"opponent": opponent, "sourceUrl": source_url, "maps": maps,
            "series": [sum(m["score"][0] > m["score"][1] for m in maps),
                       sum(m["score"][0] < m["score"][1] for m in maps)]}


def find_similar_rounds(source_url: str, map_name: str, round_number: int, limit: int = 12):
    if not DB_PATH.exists():
        return {"reference": None, "rounds": []}
    with sqlite3.connect(DB_PATH) as db:
        target_row = db.execute("SELECT opponent_key, opponent, report_json FROM map_reports WHERE source_url=? AND map_name=?",
                                (source_url, map_name)).fetchone()
        if not target_row:
            return {"reference": None, "rounds": []}
        opponent_key, opponent, target_payload = target_row
        rows_db = db.execute("SELECT source_url, opponent, map_name, report_json FROM map_reports").fetchall()
    target_report = json.loads(target_payload)
    reference = next((r for r in target_report.get("roundReview", []) if int(r.get("round") or 0) == round_number), None)
    if not reference:
        return {"reference": None, "rounds": []}

    def features(round_report, report):
        buys = round_report.get("buy", {})
        plant = round_report.get("plant") or {}
        opening = round_report.get("firstKill") or {}
        nades = {("HOTU" if n.get("team") == "HOTU" else "opponent", n.get("type"))
                 for n in round_report.get("utility", []) if n.get("type")}
        plant_time = plant.get("seconds")
        time_bucket = "early" if plant_time is not None and plant_time < 35 else "mid" if plant_time is not None and plant_time <= 70 else "late" if plant_time is not None else None
        other_team = next((name for name in buys if name != "HOTU"), None)
        winner = round_report.get("winner")
        opening_team = opening.get("killerTeam")
        return {"side": round_report.get("side"), "winner": "HOTU" if winner == "HOTU" else "opponent" if winner else None,
                "buy": (buys.get("HOTU", {}).get("buyType"), buys.get(other_team, {}).get("buyType")),
                "openingTeam": "HOTU" if opening_team == "HOTU" else "opponent" if opening_team else None,
                "plantSite": plant.get("site"),
                "plantTime": time_bucket, "nades": nades}

    ref_features = features(reference, target_report)
    matches = []
    for candidate_source, candidate_opponent, candidate_map, payload in rows_db:
        candidate_report = json.loads(payload)
        for candidate in candidate_report.get("roundReview", []):
            candidate_number = int(candidate.get("round") or 0)
            if candidate_source == source_url and candidate_map == map_name and candidate_number == round_number:
                continue
            item = features(candidate, candidate_report)
            score, reasons = 0, []
            if candidate_map == map_name:
                score += 2; reasons.append("та же карта")
            if item["side"] == ref_features["side"]:
                score += 3; reasons.append("та же сторона HOTU")
            if item["buy"] == ref_features["buy"]:
                score += 2; reasons.append("похожий класс закупа обеих команд")
            if item["openingTeam"] and item["openingTeam"] == ref_features["openingTeam"]:
                score += 1; reasons.append("та же команда взяла первый фраг")
            if item["plantSite"] and item["plantSite"] == ref_features["plantSite"]:
                score += 2; reasons.append(f"plant на {item['plantSite']}")
            if item["plantTime"] and item["plantTime"] == ref_features["plantTime"]:
                score += 1; reasons.append("сходный тайминг plant")
            union = item["nades"] | ref_features["nades"]
            nade_similarity = len(item["nades"] & ref_features["nades"]) / len(union) if union else 0
            if nade_similarity >= .5:
                score += 2; reasons.append("похожий набор типов гранат")
            if score < 4:
                continue
            matches.append({"sourceUrl": candidate_source, "map": candidate_map, "round": candidate_number,
                "opponent": candidate_opponent, "score": score, "reasons": reasons,
                "side": candidate.get("side"), "winner": candidate.get("winner"),
                "plant": candidate.get("plant"), "firstKill": candidate.get("firstKill"),
                "hltvUrl": candidate_source if candidate_source.startswith("https://") else None})
    matches.sort(key=lambda row: (row["score"], row["map"] == map_name, row["round"]), reverse=True)
    return {"reference": {"map": map_name, "round": round_number, "side": reference.get("side"),
                           "winner": reference.get("winner")}, "rounds": matches[:limit]}


class Handler(SimpleHTTPRequestHandler):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=str(HERE), **kwargs)

    def log_message(self, fmt, *args):
        print("[hotu] " + (fmt % args))

    def send_json(self, status, data):
        body = json.dumps(data, ensure_ascii=False).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        parsed = urlparse(self.path)
        if parsed.path == "/api/matches":
            return self.send_json(200, {"matches": saved_matches()})
        if parsed.path == "/api/opponents/profiles":
            return self.send_json(200, {"opponents": opponent_profiles()})
        if parsed.path == "/api/matches/load":
            source_url = parse_qs(parsed.query).get("source", [""])[0]
            match = load_saved_match(source_url)
            return self.send_json(200, match) if match else self.send_json(404, {"error": "Сохранённый матч не найден."})
        if parsed.path == "/api/rounds/similar":
            query = parse_qs(parsed.query)
            try:
                result = find_similar_rounds(query.get("source", [""])[0], query.get("map", [""])[0],
                                             int(query.get("round", ["0"])[0]))
                return self.send_json(200, result)
            except (TypeError, ValueError):
                return self.send_json(400, {"error": "Проверьте карту и номер раунда."})
        return super().do_GET()

    def do_POST(self):
        if urlparse(self.path).path != "/api/analyze":
            return self.send_json(404, {"error": "Адрес не найден"})
        try:
            if DemoParser is None:
                return self.send_json(500, {"error": "demoparser2 не установлен. См. README.md"})
            length = int(self.headers.get("Content-Length", "0"))
            if length <= 0 or length > MAX_UPLOAD:
                return self.send_json(413, {"error": "Общий размер файлов превышает лимит 1,6 ГБ."})
            # Parse multipart incrementally from the socket into temporary files.
            from email.parser import BytesParser
            from email.policy import default
            content_type = self.headers.get("Content-Type", "")
            boundary = content_type.split("boundary=", 1)[-1].strip('"')
            if not boundary:
                return self.send_json(400, {"error": "Ожидается multipart-загрузка файлов .dem."})
            # FieldStorage streams uploaded content to its own temp files without buffering in RAM.
            import cgi
            form = cgi.FieldStorage(fp=self.rfile, headers=self.headers, environ={"REQUEST_METHOD": "POST", "CONTENT_TYPE": content_type, "CONTENT_LENGTH": str(length)})
            uploads = form["demos"] if "demos" in form else []
            if not isinstance(uploads, list):
                uploads = [uploads]
            hotu_number = int(form.getfirst("hotuTeamNumber", "2"))
            opponent = safe_text(form.getfirst("opponent", "Соперник"), "Соперник")[:80]
            source_url = safe_text(form.getfirst("hltvUrl", ""), "")[:500]
            if hotu_number not in (2, 3):
                return self.send_json(400, {"error": "Выберите номер команды HOTU в демо: 2 или 3."})
            results = []
            with tempfile.TemporaryDirectory(prefix="hotu-demo-") as tmp:
                for ix, item in enumerate(uploads):
                    if not getattr(item, "filename", None):
                        continue
                    if Path(item.filename).suffix.lower() != ".dem":
                        continue
                    path = Path(tmp) / f"map-{ix}.dem"
                    with path.open("wb") as out:
                        shutil.copyfileobj(item.file, out, length=1024 * 1024)
                    results.append(analyze_demo(path, hotu_number, opponent))
            if not results:
                return self.send_json(400, {"error": "Не выбраны файлы .dem. Сначала распакуйте .rar."})
            source_key = persist_reports(opponent, source_url, results)
            for report in results:
                report["historyPatterns"] = history_for(opponent, report["name"])
            return self.send_json(200, {"opponent": opponent, "sourceUrl": source_key, "maps": results,
                                        "series": [sum(m["score"][0] > m["score"][1] for m in results),
                                                   sum(m["score"][1] > m["score"][0] for m in results)]})
        except Exception as exc:
            traceback.print_exc()
            return self.send_json(500, {"error": f"Не удалось разобрать демо: {exc}"})

    def do_OPTIONS(self):
        self.send_response(204)
        self.end_headers()


if __name__ == "__main__":
    host, port = "127.0.0.1", int(os.environ.get("HOTU_PORT", "8765"))
    print(f"HOTU Matchroom: http://{host}:{port}")
    ThreadingHTTPServer((host, port), Handler).serve_forever()
