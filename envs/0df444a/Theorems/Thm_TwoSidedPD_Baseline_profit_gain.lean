-- Prove2me | Theorems.Thm_TwoSidedPD_Baseline_profit_gain
-- name    : TwoSidedPD.Baseline.profit_gain
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:08:22.921541+00:00
-- url     : https://prove2.me/theorems/621e49b9-cb2c-4862-9010-c3c2a9d0247d
-- title:
--   App. A.2(i), p. 3352 — Π^D − Π^U = v²(θH − θL)²/(D·U) > 0
-- statement:
--   Consider the baseline two-sided platform with $\theta_H>\theta_L>0$, $b>0$ and Assumption 1; write $U=8-(2b+\theta_H+\theta_L)^2$ and $D=4-2b^2-\theta_H^2-\theta_L^2-2b(\theta_H+\theta_L)$. For every uniform-pricing optimum and every discrimination optimum,
--   $$\Pi^D-\Pi^U=\frac{v^2(\theta_H-\theta_L)^2}{D\,U}>0 .$$
--
--   This is the platform part of Proposition 2(i).
--
--   **Formalization Note.** The page prints the first factor of the denominator as $4-2b^2-\theta_H^2-\theta_L^2-2b(\theta_H-\theta_L)$; from (12) and (15) the factor is $D$, with $2b(\theta_H+\theta_L)$, and that is what is stated.
-- source:
--   de Cornière, Mantovani & Shekhar, Third-Degree Price Discrimination in Two-Sided Markets, Management Science 71(4) (2025), p. 3352, App. A.2(i), display Π^D − Π^U

import Mathlib
import Definitions.Def_TwoSidedPD_Baseline_Setting

namespace TwoSidedPD.Baseline

theorem profit_gain (v b θH θL : ℝ) (hL : 0 < θL) (hLH : θL < θH) (hb : 0 < b)
    (hA : Assumption1 v b θH θL) :
    ∀ (x : ℝ × ℝ) (y : ℝ × ℝ × ℝ), IsUniformOpt v b θH θL x → IsDiscrOpt v b θH θL y →
      profitD v b θH θL y - profitU v b θH θL x =
          v ^ 2 * (θH - θL) ^ 2 / (Dden b θH θL * Uden b θH θL) ∧
        0 < profitD v b θH θL y - profitU v b θH θL x := by sorry

end TwoSidedPD.Baseline
