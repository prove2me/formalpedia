-- Prove2me | Theorems.Thm_TSPHeuristics_NNLower_optimal_gbar
-- name    : TSPHeuristics.NNLower.optimal_gbar
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:27:45.762589+00:00
-- url     : https://prove2.me/theorems/29dd4714-f5ee-45c1-8a0b-d7566b442a8c
-- title:
--   The optimal tour of $\bar G_i$ has length $2^{i+1}-1$
-- statement:
--   For every $i\ge1$, the optimal tour of $\bar G_i$ has length equal to the number of nodes of $\bar G_i$:
--   $$\mathrm{OPTIMAL}(\bar G_i)=2^{i+1}-1.$$
--   The paper exhibits the tour that visits the nodes from left to right and returns from the right node to the start node; each of its edges has weight one.
--
--   **Formalization Note** OPTIMAL is the minimum of the tour length over all permutations; the statement is an equality, so both the upper bound (the left-to-right tour) and the lower bound (no tour is shorter) are asserted.
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, https://doi.org/10.1137/0206041, p. 568, paragraph after properties a) and b)

import Mathlib
import Definitions.Def_TSPHeuristics_NNLower_TSPModel
import Definitions.Def_TSPHeuristics_NNLower_LowerBoundFamily

namespace TSPHeuristics.NNLower

/-- p. 568: for `i ≥ 1`, `Ḡ_i` has an optimal tour whose length equals its number of nodes
`n = 2^(i+1) − 1` (the left-to-right tour, all of whose edges have weight one). -/
theorem optimal_gbar (i : ℕ) (hi : 1 ≤ i) :
    optimal (gbar i) = (2 : ℝ) ^ (i + 1) - 1 := by sorry

end TSPHeuristics.NNLower
