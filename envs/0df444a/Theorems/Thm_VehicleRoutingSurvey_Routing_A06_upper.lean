-- Prove2me | Theorems.Thm_VehicleRoutingSurvey_Routing_A06_upper
-- name    : VehicleRoutingSurvey.Routing.A06_upper
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T00:09:53.729141+00:00
-- url     : https://prove2.me/theorems/a419633a-5211-495c-8b1b-8be0022a7d96
-- title:
--   Table 3, TSP, nearest addition, upper cell
-- statement:
--   On every finite nonempty metric traveling salesman instance, every admissible nearest addition run has cost C satisfying
--
--   $$C\le 2\,\mathrm{OPT}.$$
--
--   The run constructs a full cyclic visiting order. The cost inequality also covers OPT = 0.
--
--   Differences from the source:
--   - encoding: repeat-visit undirected network TSP → complete shortest-path pseudometric with zero diagonal, and cyclic vertex orders; reason: shortest paths expand metric edges to network walks without changing attainable optimum or heuristic cost; distinct vertices may have distance zero
--   - reading: the named heuristic without pseudocode in the survey → the concrete nearest addition run relation, identified in survey reference [32], §6; reason: fixes the named procedure independently of its performance bound, retaining arbitrary legitimate ties
-- source:
--   Report 7919/O, p. 5, Table 3, TSP / nearest addition, upper cell; §4 pp. 4, 6; survey [32]. Printed p. 5; PDF 7. Algorithm definition: survey [32], Rosenkrantz–Stearns–Lewis (1977), §6, pp. 577–579; https://paperzz.com/doc/7007820/document.

import Definitions.Def_VehicleRoutingSurvey_Routing_MetricAlgorithms

namespace VehicleRoutingSurvey.Routing

theorem A06_upper :
    ∀ (n : ℕ), 1 ≤ n → ∀ (d : Fin n → Fin n → ℝ),
    TSPHeuristics.Shared.IsTSPDist d → ∀ (T : ℕ → List (Fin n)), NearestAdditionRun d T →
      TSPHeuristics.Shared.cycleLength d (T (n - 1)) ≤ 2 * TSPHeuristics.Shared.optimal d := by sorry

end VehicleRoutingSurvey.Routing
