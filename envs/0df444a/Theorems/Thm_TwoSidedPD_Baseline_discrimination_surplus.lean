-- Prove2me | Theorems.Thm_TwoSidedPD_Baseline_discrimination_surplus
-- name    : TwoSidedPD.Baseline.discrimination_surplus
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:08:10.549249+00:00
-- url     : https://prove2.me/theorems/5581093a-5691-41c3-9d04-a213d3af675f
-- title:
--   App. A.2.2, (A.6)–(A.8), p. 3352 — at the discrimination optimum CS^D = 2v²/D², DS_j^D = v²(b+θj)²/(2D²), and SW^D
-- statement:
--   Consider the baseline two-sided platform with $\theta_H>\theta_L>0$, $b>0$ and Assumption 1, and write $D=4-2b^2-\theta_H^2-\theta_L^2-2b(\theta_H+\theta_L)$. At every maximizer $(N^D_B,N^D_L,N^D_H)$ of the discriminatory profit, the buyer surplus, the surplus of type-$j$ sellers and the total welfare, defined by the integrals of App. A.2.2, equal
--   $$CS^D=\frac{2v^2}{D^2}\ \text{(A.6)},\qquad DS^D_j=\frac{v^2(b+\theta_j)^2}{2D^2}\ \text{(A.7)},$$
--   $$SW^D=CS^D+\Pi^D+DS^D_L+DS^D_H=\frac{v^2\big(12-2b^2-\theta_H^2-\theta_L^2-2b(\theta_H+\theta_L)\big)}{2D^2}\ \text{(A.8)}.$$
--
--   These are the discrimination levels compared in the proof of Proposition 2.
--
--   **Formalization Note.** The surpluses are interval integrals at an arbitrary allocation $(N_B,N_L,N_H)$; evaluating them at the optimum is the content of this statement.
-- source:
--   de Cornière, Mantovani & Shekhar, Third-Degree Price Discrimination in Two-Sided Markets, Management Science 71(4) (2025), p. 3352, App. A.2.2, displays (A.6)–(A.8)

import Mathlib
import Definitions.Def_TwoSidedPD_Baseline_Setting

namespace TwoSidedPD.Baseline

theorem discrimination_surplus (v b θH θL : ℝ) (hL : 0 < θL) (hLH : θL < θH) (hb : 0 < b)
    (hA : Assumption1 v b θH θL) :
    ∀ y : ℝ × ℝ × ℝ, IsDiscrOpt v b θH θL y →
      buyerSurplusD v b θH θL y = 2 * v ^ 2 / Dden b θH θL ^ 2 ∧
      sellerSurplusDH θH y = v ^ 2 * (b + θH) ^ 2 / (2 * Dden b θH θL ^ 2) ∧
      sellerSurplusDL θL y = v ^ 2 * (b + θL) ^ 2 / (2 * Dden b θH θL ^ 2) ∧
      welfareD v b θH θL y =
        v ^ 2 * (12 - 2 * b ^ 2 - θH ^ 2 - θL ^ 2 - 2 * b * (θH + θL)) / (2 * Dden b θH θL ^ 2) := by sorry

end TwoSidedPD.Baseline
