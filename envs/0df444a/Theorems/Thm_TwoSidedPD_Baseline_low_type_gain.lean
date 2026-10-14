-- Prove2me | Theorems.Thm_TwoSidedPD_Baseline_low_type_gain
-- name    : TwoSidedPD.Baseline.low_type_gain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:08:19.3324+00:00
-- url     : https://prove2.me/theorems/b10eea06-28e5-4c77-8536-4163b83a0b5e
-- title:
--   App. A.2(i), p. 3352 — DS_L^D − DS_L^U = ½v²((b+θL)²/D² − (2b+3θL−θH)²/U²) > 0
-- statement:
--   Consider the baseline two-sided platform with $\theta_H>\theta_L>0$, $b>0$ and Assumption 1; write $U=8-(2b+\theta_H+\theta_L)^2$ and $D=4-2b^2-\theta_H^2-\theta_L^2-2b(\theta_H+\theta_L)$. For every uniform-pricing optimum and every discrimination optimum, the surplus of low-type sellers satisfies
--   $$DS^D_L-DS^U_L=\frac12v^2\left(\frac{(b+\theta_L)^2}{D^2}-\frac{(2b+3\theta_L-\theta_H)^2}{U^2}\right)>0 .$$
--
--   This is the low-type-seller part of Proposition 2(i).
--
--   **Formalization Note.** The page prints the two fractions in the opposite order, which by A.2.1 and (A.7) is $2(DS^U_L-DS^D_L)/v^2$; the claim $DS^D_L>DS^U_L$ is the paper's, and the identity is stated with the fractions in the order that makes it true.
-- source:
--   de Cornière, Mantovani & Shekhar, Third-Degree Price Discrimination in Two-Sided Markets, Management Science 71(4) (2025), p. 3352, App. A.2(i), display DS^D_L − DS^U_L

import Mathlib
import Definitions.Def_TwoSidedPD_Baseline_Setting

namespace TwoSidedPD.Baseline

theorem low_type_gain (v b θH θL : ℝ) (hL : 0 < θL) (hLH : θL < θH) (hb : 0 < b)
    (hA : Assumption1 v b θH θL) :
    ∀ (x : ℝ × ℝ) (y : ℝ × ℝ × ℝ), IsUniformOpt v b θH θL x → IsDiscrOpt v b θH θL y →
      sellerSurplusDL θL y - sellerSurplusU θL θH θL x =
          1 / 2 * v ^ 2 * ((b + θL) ^ 2 / Dden b θH θL ^ 2 -
            (2 * b + 3 * θL - θH) ^ 2 / Uden b θH θL ^ 2) ∧
        sellerSurplusU θL θH θL x < sellerSurplusDL θL y := by sorry

end TwoSidedPD.Baseline
