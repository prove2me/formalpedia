-- Prove2me | Theorems.Thm_TSPHeuristics_NNLower_gbar_edge_lengths
-- name    : TSPHeuristics.NNLower.gbar_edge_lengths
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:26:35.011374+00:00
-- url     : https://prove2.me/theorems/e942b894-8ac7-426d-bee6-e369798d189c
-- title:
--   Property a): the edges of $G_i$ keep their lengths in $\bar G_i$
-- statement:
--   For every $i\ge1$, every edge $(a,b)$ of $G_i$ of weight $w$ is a shortest path between its endpoints:
--   $$d_{\bar G_i}(a,b)=w.$$
--   So the distances of the complete graph $\bar G_i$ restrict to the given weights on the edges of $G_i$ (property a) of p. 568).
--
--   **Formalization Note** The statement is over the edge list of $G_i$ and the shortest-path distance of that list.
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, https://doi.org/10.1137/0206041, p. 568, property a)

import Mathlib
import Definitions.Def_TSPHeuristics_NNLower_ShortestPathMetric
import Definitions.Def_TSPHeuristics_NNLower_LowerBoundFamily

namespace TSPHeuristics.NNLower

/-- Property a), p. 568: for `i ≥ 1`, every edge of `G_i` has the same length in `Ḡ_i` as in
`G_i`, i.e. each edge `(a, b, w)` of `G_i` is a shortest path: `d(a, b) = w`. -/
theorem gbar_edge_lengths (i : ℕ) (hi : 1 ≤ i) :
    ∀ e ∈ edgesG i, spDist (edgesG i) e.1 e.2.1 = e.2.2 := by sorry

end TSPHeuristics.NNLower
