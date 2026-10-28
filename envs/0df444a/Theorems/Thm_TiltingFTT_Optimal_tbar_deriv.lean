-- Prove2me | Theorems.Thm_TiltingFTT_Optimal_tbar_deriv
-- name    : TiltingFTT.Optimal.tbar_deriv
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:39.167986+00:00
-- url     : https://prove2.me/theorems/ac5f3300-60d1-41de-a76a-4b94b9593d0a
-- title:
--   Proof of Proposition 2, p. 43 — ∂T̄_L/∂τ = δ_Iδ_U F_H(F_L − F^L_H)/(δ_I F^L_H − δ_U F_L(1+τ))² < 0
-- statement:
--   Assume the standing assumptions. For every tax $\tau\ge0$ with $\delta_I\ge(1+\tau)\delta_U$, the upper bound $\bar T_L(\tau)=\frac{(\delta_I-(1+\tau)\delta_U)F_H}{\delta_IF^L_H-(1+\tau)\delta_UF_L}$ of the separating trade in state $L$ is differentiable at $\tau$ with
--   $$\frac{\partial\bar T_L}{\partial\tau}=\frac{\delta_I\delta_UF_H(F_L-F^L_H)}{\big(\delta_IF^L_H-\delta_UF_L(1+\tau)\big)^2}<0,$$
--   and $\bar T_L$ is strictly decreasing on $[0,\tau_{FB}]$, $\tau_{FB}=\delta_I/\delta_U-1$.
--
--   The negative sign comes from assumption (3), $F^L_H>F_L$. This monotonicity is what makes separating welfare fall with the tax.
-- source:
--   Dieler, Biswas, Calzolari & Castiglionesi, Asset Trade, Real Investment and a Tilting Financial Transaction Tax, accepted manuscript of January 24, 2022 (SSRN 2739357; Management Science 69(4), doi:10.1287/mnsc.2022.4417), proof of Proposition 2 (Appendix A), p. 43, "Moreover, we next show that T̄L is decreasing in τ"

import Mathlib
import Definitions.Def_TiltingFTT_Optimal_Model

namespace TiltingFTT.Optimal

theorem tbar_deriv (P : Firm) (hS : Standing P) :
    (∀ τ, 0 ≤ τ → Cond15 P τ →
      HasDerivAt (Tbar P)
        (P.δI * P.δU * P.FH * (P.FL - P.FLH) / (P.δI * P.FLH - P.δU * P.FL * (1 + τ)) ^ 2) τ ∧
      P.δI * P.δU * P.FH * (P.FL - P.FLH) / (P.δI * P.FLH - P.δU * P.FL * (1 + τ)) ^ 2 < 0) ∧
    StrictAntiOn (Tbar P) (Set.Icc 0 (tauFB P)) := by sorry

end TiltingFTT.Optimal
