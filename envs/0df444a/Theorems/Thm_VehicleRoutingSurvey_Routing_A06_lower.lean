-- Prove2me | Theorems.Thm_VehicleRoutingSurvey_Routing_A06_lower
-- name    : VehicleRoutingSurvey.Routing.A06_lower
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T00:09:45.976882+00:00
-- url     : https://prove2.me/theorems/cda4d4c9-842d-4f81-98a4-733cbdc8967b
-- title:
--   Table 3, TSP, nearest addition, lower cell
-- statement:
--   For every epsilon > 0 and vertex threshold N, there is a metric traveling salesman instance with v >= N, positive optimum OPT, and an admissible nearest addition run whose cost C satisfies
--
--   $$C>(2-\varepsilon)\,\mathrm{OPT}.$$
--
--   This is the asymptotic lower cell of Table 3. It concerns this same algorithm and permits witnesses on an unbounded subsequence of sizes.
--
--   Differences from the source:
--   - encoding: repeat-visit undirected network TSP → complete shortest-path pseudometric with zero diagonal, and cyclic vertex orders; reason: shortest paths expand metric edges to network walks without changing attainable optimum or heuristic cost; distinct vertices may have distance zero
--   - reading: the named heuristic without pseudocode in the survey → the concrete nearest addition run relation, identified in survey reference [32], §6; reason: fixes the named procedure independently of its performance bound, retaining arbitrary legitimate ties
--   - encoding: asymptotic bad instances, deleting vanishing terms → for every positive epsilon and size threshold, a larger positive-OPT instance exceeds the displayed bound minus epsilon; reason: arbitrarily large witnesses preserve the report convention without asserting a witness at every size
-- source:
--   Report 7919/O, p. 5, Table 3, TSP / nearest addition, lower cell; §4 pp. 4, 6; survey [32]. Printed p. 5; PDF 7. Algorithm definition: survey [32], Rosenkrantz–Stearns–Lewis (1977), §6, pp. 577–579; https://paperzz.com/doc/7007820/document.

import Definitions.Def_VehicleRoutingSurvey_Routing_MetricAlgorithms

namespace VehicleRoutingSurvey.Routing

theorem A06_lower :
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
    ∃ (n : ℕ) (d : Fin n → Fin n → ℝ) (T : ℕ → List (Fin n)),
      N ≤ n ∧ 1 ≤ n ∧ TSPHeuristics.Shared.IsTSPDist d ∧
      0 < TSPHeuristics.Shared.optimal d ∧ NearestAdditionRun d T ∧
      (2 - ε) * TSPHeuristics.Shared.optimal d < TSPHeuristics.Shared.cycleLength d (T (n - 1)) := by sorry

end VehicleRoutingSurvey.Routing
