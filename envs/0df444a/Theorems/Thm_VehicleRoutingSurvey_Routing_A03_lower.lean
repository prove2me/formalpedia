-- Prove2me | Theorems.Thm_VehicleRoutingSurvey_Routing_A03_lower
-- name    : VehicleRoutingSurvey.Routing.A03_lower
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T00:09:50.647753+00:00
-- url     : https://prove2.me/theorems/97f0244f-584a-4a9d-9dd9-dc4689df4fe5
-- title:
--   Table 3, TSP, insertion, lower cell
-- statement:
--   For every epsilon > 0 and vertex threshold N, there is a metric traveling salesman instance with v >= N, positive optimum OPT, and an admissible arbitrary insertion run whose cost C satisfies
--
--   $$C>(4-\varepsilon)\,\mathrm{OPT}.$$
--
--   This is the asymptotic lower cell of Table 3. It concerns this same algorithm and permits witnesses on an unbounded subsequence of sizes.
--
--   Differences from the source:
--   - encoding: repeat-visit undirected network TSP → complete shortest-path pseudometric with zero diagonal, and cyclic vertex orders; reason: shortest paths expand metric edges to network walks without changing attainable optimum or heuristic cost; distinct vertices may have distance zero
--   - encoding: asymptotic bad instances, deleting vanishing terms → for every positive epsilon and size threshold, a larger positive-OPT instance exceeds the displayed bound minus epsilon; reason: arbitrarily large witnesses preserve the report convention without asserting a witness at every size
-- source:
--   Report 7919/O, p. 5, Table 3, TSP / insertion, lower cell; §4 pp. 4, 6; survey [32]. Printed p. 5; PDF 7.

import Definitions.Def_VehicleRoutingSurvey_Routing_MetricAlgorithms

namespace VehicleRoutingSurvey.Routing

theorem A03_lower :
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
    ∃ (n : ℕ) (d : Fin n → Fin n → ℝ) (T : ℕ → List (Fin n)) (a : ℕ → Fin n),
      N ≤ n ∧ 1 ≤ n ∧ TSPHeuristics.Shared.IsTSPDist d ∧
      0 < TSPHeuristics.Shared.optimal d ∧ TSPHeuristics.Shared.IsInsertionRun d T a ∧
      (4 - ε) * TSPHeuristics.Shared.optimal d < TSPHeuristics.Shared.cycleLength d (T n) := by sorry

end VehicleRoutingSurvey.Routing
