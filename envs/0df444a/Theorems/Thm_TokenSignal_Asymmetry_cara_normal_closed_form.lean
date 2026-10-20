-- Prove2me | Theorems.Thm_TokenSignal_Asymmetry_cara_normal_closed_form
-- name    : TokenSignal.Asymmetry.cara_normal_closed_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:18:52.36937+00:00
-- url     : https://prove2.me/theorems/7e87282b-abe9-4536-98ea-4b858d89e476
-- title:
--   Equation (38): CARA-normal closed form
-- statement:
--   In the two-type normal-revenue model, expected revenue under belief $j$ is $\mathbb E_j[R_j]=\mu_j/4$. For every actual type $i$, believed type $j$, and sale fraction $0\le\alpha\le1$, expected CARA utility has the closed form
--
--   $$U_{ij}(\alpha)=\gamma^{-1}-\gamma^{-1}\exp\!\left[-\gamma\left(V_{ij}(\alpha)-C-I\right)\right],\qquad V_{ij}(\alpha)=\frac{\alpha\mu_j+(1-\alpha)\mu_i}{4}-\frac{\gamma(1-\alpha)^2\sigma^2}{32}.$$
--
--   This identifies the certainty equivalent used to compare the two types’ incentive constraints.
-- source:
--   Chod & Lyandres, A Theory of ICOs: Diversification, Agency, and Information Asymmetry, SSRN 3159528 (version of Dec. 14, 2019), p. 31 (PDF 32), proof of Proposition 5, eq. (38)

import Mathlib
import Definitions.Def_TokenSignal_Asymmetry_Model

namespace TokenSignal.Asymmetry

theorem cara_normal_closed_form (P : Params) (hS : P.Standing) :
    (∀ j : Ty, ER P j = P.μ j / 4) ∧
    (∀ (i j : Ty) (α : ℝ), 0 ≤ α → α ≤ 1 →
      U P i j α = P.γ⁻¹ - P.γ⁻¹ * Real.exp (-(P.γ * (V P i j α - P.C - P.I)))) := by sorry
end TokenSignal.Asymmetry
