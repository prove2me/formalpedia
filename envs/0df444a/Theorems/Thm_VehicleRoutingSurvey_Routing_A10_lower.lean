-- Prove2me | Theorems.Thm_VehicleRoutingSurvey_Routing_A10_lower
-- name    : VehicleRoutingSurvey.Routing.A10_lower
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T00:09:51.648048+00:00
-- url     : https://prove2.me/theorems/584f0f7c-38c6-43ae-a9fd-d83cd5920b3e
-- title:
--   Table 3, TSP, spanning tree + matching, lower cell
-- statement:
--   For every epsilon > 0 and vertex threshold N, there is a metric traveling salesman instance with v >= N, positive optimum OPT, and an admissible spanning tree plus matching (Christofides) run whose cost C satisfies
--
--   $$C>(3/2-\varepsilon)\,\mathrm{OPT}.$$
--
--   This is the asymptotic lower cell of Table 3. It concerns this same algorithm and permits witnesses on an unbounded subsequence of sizes.
--
--   Differences from the source:
--   - encoding: repeat-visit undirected network TSP → complete shortest-path pseudometric with zero diagonal, and cyclic vertex orders; reason: shortest paths expand metric edges to network walks without changing attainable optimum or heuristic cost; distinct vertices may have distance zero
--   - encoding: asymptotic bad instances, deleting vanishing terms → for every positive epsilon and size threshold, a larger positive-OPT instance exceeds the displayed bound minus epsilon; reason: arbitrarily large witnesses preserve the report convention without asserting a witness at every size
-- source:
--   Report 7919/O, p. 5, Table 3, TSP / spanning tree + matching, lower cell; §4 pp. 4, 6; survey [3;5]. Printed p. 5; PDF 7.

import Definitions.Def_VehicleRoutingSurvey_Routing_MetricAlgorithms

namespace VehicleRoutingSurvey.Routing

theorem A10_lower :
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
    ∃ (n : ℕ) (d : Fin n → Fin n → ℝ) (τ : Equiv.Perm (Fin n)),
      N ≤ n ∧ 1 ≤ n ∧ SupplyChainTheory.IsMetric d ∧
      0 < SupplyChainTheory.optTourLength d ∧ ChristofidesRun d τ ∧
      (3 / 2 - ε) * SupplyChainTheory.optTourLength d < SupplyChainTheory.tourLength d τ := by sorry

end VehicleRoutingSurvey.Routing
