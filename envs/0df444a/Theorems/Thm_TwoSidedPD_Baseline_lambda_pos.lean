-- Prove2me | Theorems.Thm_TwoSidedPD_Baseline_lambda_pos
-- name    : TwoSidedPD.Baseline.lambda_pos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:08:19.363269+00:00
-- url     : https://prove2.me/theorems/8201906a-3db2-459a-ac4b-4787365609d9
-- title:
--   App. A.2(ii), p. 3353 — λ > 0 on the admissible parameter region
-- statement:
--   Let $v,b,\theta_H,\theta_L$ be real numbers with $\theta_H>\theta_L>0$, $b>0$ and Assumption 1:
--   $$0<v<4-(b+\theta_L)^2-(b+\theta_H)^2,\qquad \frac{\theta_H-3\theta_L}{2}<b .$$
--   Then the quartic
--   $$\lambda=32-24b^4-7\theta_H^4+2\theta_H^3\theta_L+28\theta_L^2-7\theta_L^4-48b^3(\theta_H+\theta_L)-2\theta_L\theta_H(12-\theta_L^2)+14\theta_H^2(2-\theta_L^2)+2b(\theta_H+\theta_L)(16-13\theta_H^2+2\theta_H\theta_L-13\theta_L^2)+2b^2(16-25\theta_H^2-22\theta_L\theta_H-25\theta_L^2)$$
--   is strictly positive.
--
--   Together with the welfare identity, this gives Proposition 2(ii): total welfare is higher under price discrimination.
--
--   **Formalization Note.** The paper states the conclusion for $b<\bar b(\theta_H,\theta_L,v)$, the boundary of $2v<4-(b+\theta_L)^2-(b+\theta_H)^2$; the statement here uses Assumption 1(i) as printed ($v<\dots$), a larger region, so it is at least as strong as the paper's. The parameter $v$ enters only through Assumption 1.
-- source:
--   de Cornière, Mantovani & Shekhar, Third-Degree Price Discrimination in Two-Sided Markets, Management Science 71(4) (2025), p. 3353, App. A.2(ii), 'for b < b̄(θH, θL, v) < b^sol(θH, θL), we must have λ > 0'

import Mathlib
import Definitions.Def_TwoSidedPD_Baseline_Setting

namespace TwoSidedPD.Baseline

theorem lambda_pos (v b θH θL : ℝ) (hL : 0 < θL) (hLH : θL < θH) (hb : 0 < b)
    (hA : Assumption1 v b θH θL) :
    0 < lam b θH θL := by sorry

end TwoSidedPD.Baseline
