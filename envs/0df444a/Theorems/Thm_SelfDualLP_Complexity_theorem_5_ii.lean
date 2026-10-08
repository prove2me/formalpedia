-- Prove2me | Theorems.Thm_SelfDualLP_Complexity_theorem_5_ii
-- name    : SelfDualLP.Complexity.theorem_5_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:59:57.811992+00:00
-- url     : https://prove2.me/theorems/d3839f2c-8215-408c-aaec-5b9640e3ae78
-- title:
--   Theorem 5 (ii) — directions in the null space $Q$ satisfy $d_x^Td_s+d_\tau d_\kappa=0$
-- statement:
--   Work under the choice (7). Let $(d_y,d_x,d_\tau,d_\theta,d_s,d_\kappa)$ lie in the null space $Q$ of the constraint matrix of (HLP) after adding the surplus variables $s$ and $\kappa$, i.e.
--   $$
--   \begin{aligned}
--   Ad_x-bd_\tau+\bar bd_\theta&=0,\\
--   -A^Td_y+cd_\tau-\bar cd_\theta-d_s&=0,\\
--   b^Td_y-c^Td_x+\bar zd_\theta-d_\kappa&=0,\\
--   -\bar b^Td_y+\bar c^Td_x-\bar zd_\tau&=0 .
--   \end{aligned}
--   $$
--   Then
--   $$
--   (d_x)^Td_s+d_\tau d_\kappa=0 .
--   $$
--
--   This orthogonality is what makes the predictor–corrector analysis of the standard primal–dual setting apply verbatim to (HLP).
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), p. 59, Theorem 5 (ii)

import Mathlib
import Definitions.Def_SelfDualLP_Complexity_HLP
import Definitions.Def_SelfDualLP_Complexity_Neighborhood

open Matrix

namespace SelfDualLP.Complexity

/-- Theorem 5 (ii) (p. 59), under the choice (7). If `(d_y, d_x, d_τ, d_θ, d_s, d_κ)` lies in the
null space `Q` of the constraint matrix of (HLP) after adding surplus variables `s` and `κ`, then
`(d_x)ᵀd_s + d_τ d_κ = 0`. -/
theorem theorem_5_ii {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (d : HLPPoint m n) (hd : InQ7 A b c d) :
    d.x ⬝ᵥ d.s + d.τ * d.κ = 0 := by sorry

end SelfDualLP.Complexity
