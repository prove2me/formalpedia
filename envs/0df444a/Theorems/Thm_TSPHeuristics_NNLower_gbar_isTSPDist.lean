-- Prove2me | Theorems.Thm_TSPHeuristics_NNLower_gbar_isTSPDist
-- name    : TSPHeuristics.NNLower.gbar_isTSPDist
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:25:31.997576+00:00
-- url     : https://prove2.me/theorems/076b48aa-477f-4c2f-978c-10d9b65b6c24
-- title:
--   $\bar G_i$ is a traveling salesman graph
-- statement:
--   For every $i\ge1$, let $\bar G_i$ be the complete graph on the $2^{i+1}-1$ nodes of $G_i$ in which $d(a,b)$ is the length of a minimal path from $a$ to $b$ in $G_i$. Then $d$ is a traveling salesman distance: for all nodes $a,b,c$,
--   $$d(a,b)=d(b,a),\qquad d(a,b)\ge0,\qquad d(a,c)\le d(a,b)+d(b,c),\qquad d(a,a)=0.$$
--
--   This is what makes $\bar G_i$ an admissible instance for Theorem 2.
--
--   **Formalization Note** The last property is the normalization field of `IsTSPDist`, not in the paper.
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, https://doi.org/10.1137/0206041, p. 568 ("Therefore, the distances in Ḡ_i satisfy the triangle inequality.")

import Mathlib
import Definitions.Def_TSPHeuristics_NNLower_TSPModel
import Definitions.Def_TSPHeuristics_NNLower_LowerBoundFamily

namespace TSPHeuristics.NNLower

/-- p. 568: for every `i ≥ 1`, the shortest-path distance of `G_i` makes `Ḡ_i` a traveling
salesman graph (symmetric, nonnegative, zero on the diagonal, triangle inequality). -/
theorem gbar_isTSPDist (i : ℕ) (hi : 1 ≤ i) : IsTSPDist (gbar i) := by sorry

end TSPHeuristics.NNLower
