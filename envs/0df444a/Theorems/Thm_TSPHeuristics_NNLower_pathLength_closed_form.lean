-- Prove2me | Theorems.Thm_TSPHeuristics_NNLower_pathLength_closed_form
-- name    : TSPHeuristics.NNLower.pathLength_closed_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:24:40.389131+00:00
-- url     : https://prove2.me/theorems/8dcb7a96-e2e5-4553-9384-bca4b71eacad
-- title:
--   Eq. (2.12): $L_i=\frac19(6 i 2^i+8\cdot2^i+(-1)^i-9)$
-- statement:
--   Let $l_i=\frac16(4\cdot 2^i-(-1)^i+3)$ as in (2.11), and let $L_i$ be defined by $L_1=2$ and $L_{i+1}=2L_i+2l_i$. Then for every $i\ge1$,
--   $$L_i=\tfrac19\bigl(6\cdot i\cdot 2^i+8\cdot 2^i+(-1)^i-9\bigr).$$
--
--   $L_i$ is the length of the path $P_i$ in the graph $F_i$ of the proof of Theorem 2; the closed form is what makes the ratio of the lower-bound instance computable.
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, https://doi.org/10.1137/0206041, p. 567, eq. (2.12)

import Mathlib
import Definitions.Def_TSPHeuristics_NNLower_LowerBoundFamily

namespace TSPHeuristics.NNLower

/-- Eq. (2.12), p. 567: the solution of `L_{i+1} = 2 L_i + 2 l_i`, `L_1 = 2`, with `l_i` as in
(2.11), is `L_i = (1/9)(6 · i · 2^i + 8 · 2^i + (−1)^i − 9)` for every `i ≥ 1`. -/
theorem pathLength_closed_form (i : ℕ) (hi : 1 ≤ i) :
    pathLength i = (6 * (i : ℝ) * 2 ^ i + 8 * 2 ^ i + (-1) ^ i - 9) / 9 := by sorry

end TSPHeuristics.NNLower
