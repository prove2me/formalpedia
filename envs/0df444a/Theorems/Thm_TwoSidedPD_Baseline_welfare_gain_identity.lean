-- Prove2me | Theorems.Thm_TwoSidedPD_Baseline_welfare_gain_identity
-- name    : TwoSidedPD.Baseline.welfare_gain_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:08:18.926021+00:00
-- url     : https://prove2.me/theorems/a08a9d68-0cec-40a6-ba2d-16106fd193d4
-- title:
--   App. A.2(ii), p. 3352 — SW^D − SW^U = v²(θH − θL)²λ/(2D²U²) with the quartic λ
-- statement:
--   Consider the baseline two-sided platform with $\theta_H>\theta_L>0$, $b>0$ and Assumption 1; write $U=8-(2b+\theta_H+\theta_L)^2$ and $D=4-2b^2-\theta_H^2-\theta_L^2-2b(\theta_H+\theta_L)$. For every uniform-pricing optimum and every discrimination optimum,
--   $$SW^D-SW^U=\frac{v^2(\theta_H-\theta_L)^2\,\lambda}{2D^2U^2},$$
--   where
--   $$\lambda=32-24b^4-7\theta_H^4+2\theta_H^3\theta_L+28\theta_L^2-7\theta_L^4-48b^3(\theta_H+\theta_L)-2\theta_L\theta_H(12-\theta_L^2)+14\theta_H^2(2-\theta_L^2)+2b(\theta_H+\theta_L)(16-13\theta_H^2+2\theta_H\theta_L-13\theta_L^2)+2b^2(16-25\theta_H^2-22\theta_L\theta_H-25\theta_L^2).$$
--
--   The sign of the welfare change is therefore the sign of $\lambda$, which reduces Proposition 2(ii) to a polynomial inequality.
--
--   **Formalization Note.** The page's denominator prints $\theta_l$ inside $U$; it is $\theta_L$. $\lambda$ is transcribed term by term as printed.
-- source:
--   de Cornière, Mantovani & Shekhar, Third-Degree Price Discrimination in Two-Sided Markets, Management Science 71(4) (2025), p. 3352, App. A.2(ii), display SW^D − SW^U and the definition of λ

import Mathlib
import Definitions.Def_TwoSidedPD_Baseline_Setting

namespace TwoSidedPD.Baseline

theorem welfare_gain_identity (v b θH θL : ℝ) (hL : 0 < θL) (hLH : θL < θH) (hb : 0 < b)
    (hA : Assumption1 v b θH θL) :
    ∀ (x : ℝ × ℝ) (y : ℝ × ℝ × ℝ), IsUniformOpt v b θH θL x → IsDiscrOpt v b θH θL y →
      welfareD v b θH θL y - welfareU v b θH θL x =
        v ^ 2 * (θH - θL) ^ 2 * lam b θH θL / (2 * Dden b θH θL ^ 2 * Uden b θH θL ^ 2) := by sorry

end TwoSidedPD.Baseline
