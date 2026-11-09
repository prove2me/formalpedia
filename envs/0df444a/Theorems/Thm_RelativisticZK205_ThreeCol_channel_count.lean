-- Prove2me | Theorems.Thm_RelativisticZK205_ThreeCol_channel_count
-- name    : RelativisticZK205.ThreeCol.channel_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:18:06.369967+00:00
-- url     : https://prove2.me/theorems/4661a56e-5977-48af-8525-7f43fc3dae74
-- title:
--   p.11 — the simulators use at most $8\lceil\log_2|V|\rceil$ PR-boxes and one 3-COLZK, at most $8\lceil\log_2|V|\rceil+1$ channels
-- statement:
--   Let $G$ be a graph on $n=|V|$ vertices. The simulators' wiring uses
--
--   1. at most $8\lceil\log_2|V|\rceil$ PR-boxes,
--   2. exactly one 3-COLZK channel,
--
--   and therefore at most
--
--   $$
--   8\lceil\log_2|V|\rceil+1
--   $$
--
--   channel instances in total, a number polynomial in $|V|$.
--
--   Differences from the source:
--   - reading: 8⌈log(|V|)⌉ + 1, log written without base in the final sentence → 8 * Nat.clog 2 n + 1; reason: the preceding sentences of the paragraph write ⌈log₂(|V|)⌉
--   - encoding: a graph G on the labels 0, …, |V|−1, with query bits in F₂ → G : SimpleGraph (Fin n) with decidable adjacency, Query n := Fin n × Fin n × Bool; reason: Fin n is the source label set and Bool is its two-element query alphabet; finite adjacency admits a decision procedure
--   - encoding: h = ⌈log₂ |V|⌉ and h − 1 comparator iterations → Nat.clog 2 n and truncated h − 1, including n = 0 and n = 1; reason: for n ≥ 1 Nat.clog is the ceiling logarithm; for n ≤ 1 there are no valid edge queries, the PR loop is empty, and the fixed wiring reserves one unused 3-COLZK instance
-- source:
--   Claude Crépeau, Harmanpreet Singh Grover, April Niu, Nan Yang, Fadi Younes, Relativistic Zero Knowledge, STOC 2027 submission #205 (October 2026), p.11, paragraph "Simulator complexity in terms of number of channels required"

import Mathlib
import Definitions.Def_RelativisticZK205_ThreeCol_Simulator

namespace RelativisticZK205.ThreeCol

/-- p.11, simulator complexity: the simulator wiring uses at most `8⌈log₂ |V|⌉` PR-boxes and exactly
one 3-COLZK channel, hence at most `8⌈log₂ |V|⌉ + 1` channels in total. -/
theorem channel_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (simWiring G).uses SimBox.pr ≤ 8 * Nat.clog 2 n ∧
    (simWiring G).uses SimBox.colzk = 1 ∧
    (simWiring G).size ≤ 8 * Nat.clog 2 n + 1 := by sorry

end RelativisticZK205.ThreeCol
