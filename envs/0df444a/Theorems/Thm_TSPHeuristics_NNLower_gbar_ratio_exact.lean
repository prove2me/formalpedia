-- Prove2me | Theorems.Thm_TSPHeuristics_NNLower_gbar_ratio_exact
-- name    : TSPHeuristics.NNLower.gbar_ratio_exact
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:28:08.722677+00:00
-- url     : https://prove2.me/theorems/7493e497-cb53-4512-96ff-4cd57fc63847
-- title:
--   The ratio of $\bar G_i$ is exactly $(L_i+l_i-1)/n$
-- statement:
--   Let $i\ge1$, $n=2^{i+1}-1$, and let $\tau$ be the tour of $\bar G_i$ that visits the nodes in the order of the path $P_i$ and returns to the start node. Then
--   $$\mathrm{len}_{\bar G_i}(\tau)=L_i+l_i-1\qquad\text{and}\qquad \frac{\mathrm{len}_{\bar G_i}(\tau)}{\mathrm{OPTIMAL}(\bar G_i)}=\frac{L_i+l_i-1}{n}.$$
--   Together with property b), this is the ratio NEARNEIBER/OPTIMAL of the instance $\bar G_{m-1}$ (p. 569, where $i=\lg(n+1)-1$).
--
--   **Formalization Note** $L_i$ is the solution of $L_1=2$, $L_{i+1}=2L_i+2l_i$.
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, https://doi.org/10.1137/0206041, p. 569, first display

import Mathlib
import Definitions.Def_TSPHeuristics_NNLower_TSPModel
import Definitions.Def_TSPHeuristics_NNLower_LowerBoundFamily

namespace TSPHeuristics.NNLower

/-- p. 569: for `i ≥ 1`, the tour of `Ḡ_i` visiting the nodes in the order of `P_i` has length
`L_i + l_i − 1`, and its ratio to the optimal tour is exactly `(L_i + l_i − 1)/n` with
`n = 2^(i+1) − 1`. -/
theorem gbar_ratio_exact (i : ℕ) (hi : 1 ≤ i) (τ : Equiv.Perm (Fin (numNodes i)))
    (hτ : ∀ k : Fin (numNodes i), (τ k : ℕ) = (pathP i).getD k 0) :
    tourLength (gbar i) τ = pathLength i + ell i - 1 ∧
      tourLength (gbar i) τ / optimal (gbar i) =
        (pathLength i + ell i - 1) / ((2 : ℝ) ^ (i + 1) - 1) := by sorry

end TSPHeuristics.NNLower
