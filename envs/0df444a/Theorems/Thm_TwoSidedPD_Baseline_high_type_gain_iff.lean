-- Prove2me | Theorems.Thm_TwoSidedPD_Baseline_high_type_gain_iff
-- name    : TwoSidedPD.Baseline.high_type_gain_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:08:22.727901+00:00
-- url     : https://prove2.me/theorems/894bd55c-4aca-4be2-a8b0-c058b377c2b4
-- title:
--   App. A.2(iii), p. 3353 — DS_H^D − DS_H^U = ½v²((b+θH)²/D² − (2b+3θH−θL)²/U²) > 0 iff b > b̂(θH, θL)
-- statement:
--   Consider the baseline two-sided platform with $\theta_H>\theta_L>0$, $b>0$ and Assumption 1; write $U=8-(2b+\theta_H+\theta_L)^2$ and $D=4-2b^2-\theta_H^2-\theta_L^2-2b(\theta_H+\theta_L)$. For every uniform-pricing optimum and every discrimination optimum, the surplus of high-type sellers satisfies
--   $$DS^D_H-DS^U_H=\frac12v^2\left(\frac{(b+\theta_H)^2}{D^2}-\frac{(2b+3\theta_H-\theta_L)^2}{U^2}\right),$$
--   and
--   $$DS^D_H>DS^U_H\iff b>\hat b(\theta_H,\theta_L)=\frac{\sqrt{32-7(\theta_H-\theta_L)^2}-3\theta_H-\theta_L}{4}.$$
--
--   This is Proposition 2(iii).
--
--   **Formalization Note.** As for low-type sellers, the page prints the two fractions in the opposite order; the identity is stated with the fractions in the order that makes it true, and the paper's claim (iii) is unchanged. The square root is `Real.sqrt`; on the parameter region $32-7(\theta_H-\theta_L)^2>0$.
-- source:
--   de Cornière, Mantovani & Shekhar, Third-Degree Price Discrimination in Two-Sided Markets, Management Science 71(4) (2025), p. 3353, App. A.2(iii), display DS^D_H − DS^U_H

import Mathlib
import Definitions.Def_TwoSidedPD_Baseline_Setting

namespace TwoSidedPD.Baseline

theorem high_type_gain_iff (v b θH θL : ℝ) (hL : 0 < θL) (hLH : θL < θH) (hb : 0 < b)
    (hA : Assumption1 v b θH θL) :
    ∀ (x : ℝ × ℝ) (y : ℝ × ℝ × ℝ), IsUniformOpt v b θH θL x → IsDiscrOpt v b θH θL y →
      sellerSurplusDH θH y - sellerSurplusU θH θH θL x =
          1 / 2 * v ^ 2 * ((b + θH) ^ 2 / Dden b θH θL ^ 2 -
            (2 * b + 3 * θH - θL) ^ 2 / Uden b θH θL ^ 2) ∧
        (sellerSurplusU θH θH θL x < sellerSurplusDH θH y ↔ bhat θH θL < b) := by sorry

end TwoSidedPD.Baseline
