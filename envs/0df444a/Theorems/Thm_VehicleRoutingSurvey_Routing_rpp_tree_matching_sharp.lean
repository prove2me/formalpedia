-- Prove2me | Theorems.Thm_VehicleRoutingSurvey_Routing_rpp_tree_matching_sharp
-- name    : VehicleRoutingSurvey.Routing.rpp_tree_matching_sharp
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T00:13:39.29829+00:00
-- url     : https://prove2.me/theorems/308b95e7-2cc4-4fd3-98b4-3b1ae6cb9c6a
-- title:
--   Table 3 — sharp three-halves rural postman approximation and runtime
-- statement:
--   For every finite connected undirected network with nonnegative real link weights and an arbitrary required-edge subset, the spanning-tree-plus-matching rural postman procedure has an admissible run. Every such run is a feasible closed service walk, and its cost C satisfies
--
--   $$C\le\frac32\,\mathrm{OPT}.$$
--
--   The optimum is attained by a feasible walk. For every epsilon > 0 and threshold N, an instance with at least N vertices and positive optimum has an admissible run satisfying
--
--   $$C>(\tfrac32-\varepsilon)\,\mathrm{OPT}.$$
--
--   Finally, there is one finite arithmetic program implementing the procedure and constants C0 > 0 and N0, independent of instances and weights, whose operation count is at most C0(v^3+e) when v+e >= N0. It halts correctly also below this threshold. The three clauses retain the entire RPP row; no connected-required-subgraph or integer-weight restriction is imposed.
--
--   Differences from the source:
--   - reading: RPP spanning tree plus matching → minimum tree between required components, shortest-path expansion, odd-vertex minimum matching and Euler tour preserving every required edge; reason: makes the named procedure explicit as specified by the brief, without requiring the required subgraph to be connected
--   - encoding: asymptotic bad instances, deleting vanishing terms → for every positive epsilon and size threshold, a larger positive-OPT instance exceeds the displayed bound minus epsilon; reason: arbitrarily large witnesses preserve the report convention without asserting a witness at every size
--   - encoding: O(v^3+e) operations → one finite arithmetic RAM program and uniform positive C and threshold N before quantifying over real-weight instances; reason: counts arithmetic and memory operations, not bits; no constant depends on the input weights
--   - encoding: finite connected network and minimum tour weight → nonempty Fin-indexed mixed-link representation restricted to undirected networks; infimum with attained feasible minimum asserted; reason: nonnegative costs and connectivity supply a finite attained minimum; empty service has a zero-cost idle tour
-- source:
--   Lenstra and Rinnooy Kan, Complexity of vehicle routing and scheduling problems, Econometric Institute Report 7919/O (1979), p. 5 (PDF 7), Table 3 RPP / spanning tree + matching, upper, lower and complexity cells [9]; §4 pp. 4, 6.

import Definitions.Def_VehicleRoutingSurvey_Routing_RuralRuntime

namespace VehicleRoutingSurvey.Routing

theorem rpp_tree_matching_sharp :
    (∀ I : Service, Rural I →
      (∃ u ts, RuralRun I u ts) ∧
      (∃ u ts, Feasible I u ts ∧ pathCost I.graph ts = optimum I) ∧
      (∀ u ts, RuralRun I u ts → Feasible I u ts ∧
        pathCost I.graph ts ≤ (3 / 2 : ℝ) * optimum I)) ∧
    (∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
      ∃ (I : Service) (u : Fin I.graph.n) (ts : List (Traversal I.graph)),
        Rural I ∧ N ≤ I.graph.n ∧ 0 < optimum I ∧ RuralRun I u ts ∧
        (3 / 2 - ε) * optimum I < pathCost I.graph ts) ∧
    (∃ (p : List ArithmeticInstruction) (C N : ℕ), RuralImplementation p C N) := by sorry

end VehicleRoutingSurvey.Routing
