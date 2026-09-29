-- Prove2me | Theorems.Thm_TSPHeuristics_KOpt_theorem_5_proof_circle_lengths
-- name    : TSPHeuristics.KOpt.theorem_5_proof_circle_lengths
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:57:00.457908+00:00
-- url     : https://prove2.me/theorems/5dbbbc22-0879-48e4-9e9f-e79b7d987e58
-- title:
--   Proof of Theorem 5: $T_n$ has length $2(n-1)$ and OPTIMAL $= n$ on the circle
-- statement:
--   Let $n\ge 6$. On the circle graph $(N_n,d_n)$ the final subtour $T_n$ of the proof of Theorem 5 has two edges of length one and $n-2$ edges of length two, and the optimal tour visits the nodes in numerical order:
--   $$\ell(T_n)=2(n-1),\qquad \mathrm{OPTIMAL}=n.$$
--
--   Dividing the two gives the ratio $2(1-1/n)$ of Theorem 5, (4.14).
--
--   **Formalization Note** $T_n$ is the list `circleSubtour n n` (0-based nodes). OPTIMAL is the true minimum over all tours (`Finset.inf'`), so the second equality asserts both that the numerical-order tour has length $n$ and that no tour is shorter.
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, p. 576, proof of Theorem 5, last paragraph ('We note finally that the approximation T_n has two edges of length one …')

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel
import Definitions.Def_TSPHeuristics_KOpt_CircleInstance

namespace TSPHeuristics.KOpt

theorem theorem_5_proof_circle_lengths (n : ℕ) (hn : 6 ≤ n) :
    TSPHeuristics.Shared.cycleLength (cycDist n) (circleSubtour n n) = 2 * ((n : ℝ) - 1) ∧
      TSPHeuristics.Shared.optimal (cycDist n) = n := by sorry

end TSPHeuristics.KOpt
