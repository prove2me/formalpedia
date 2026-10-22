-- Prove2me | Theorems.Thm_TwoSidedPD_Baseline_uniform_surplus
-- name    : TwoSidedPD.Baseline.uniform_surplus
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:08:08.314981+00:00
-- url     : https://prove2.me/theorems/efae7525-e99e-411b-bc2c-d7823dcc80fa
-- title:
--   App. A.2.1, p. 3352 — at the uniform optimum CS^U = 8v²/U², DS_j^U = v²(2b+3θj−θ−j)²/(2U²), and SW^U
-- statement:
--   Consider the baseline two-sided platform with $\theta_H>\theta_L>0$, $b>0$ and Assumption 1, and write $U=8-(2b+\theta_H+\theta_L)^2$. At every maximizer $(N^U_B,N^U_S)$ of the uniform-pricing profit, the buyer surplus, the surplus of type-$j$ sellers and the total welfare, defined by the integrals of App. A.2.1, equal
--   $$CS^U=\frac{8v^2}{U^2},\qquad DS^U_j=\frac{v^2(2b+3\theta_j-\theta_{-j})^2}{2U^2}\ (j\in\{L,H\}),$$
--   $$SW^U=CS^U+\Pi^U+DS^U_L+DS^U_H=\frac{v^2\big(24-(2b+3\theta_H-\theta_L)(2b-\theta_H+3\theta_L)\big)}{U^2}.$$
--
--   These are the uniform-pricing levels compared in the proof of Proposition 2.
--
--   **Formalization Note.** The surpluses are defined as interval integrals at an arbitrary allocation; evaluating them at the optimum is the content of this statement. The paper writes the seller sum as $\sum_{i=1,2}DS^U_j$; it is $DS^U_L+DS^U_H$.
-- source:
--   de Cornière, Mantovani & Shekhar, Third-Degree Price Discrimination in Two-Sided Markets, Management Science 71(4) (2025), p. 3352, App. A.2.1 (displays CS^U, DS^U_j, SW^U)

import Mathlib
import Definitions.Def_TwoSidedPD_Baseline_Setting

namespace TwoSidedPD.Baseline

theorem uniform_surplus (v b θH θL : ℝ) (hL : 0 < θL) (hLH : θL < θH) (hb : 0 < b)
    (hA : Assumption1 v b θH θL) :
    ∀ x : ℝ × ℝ, IsUniformOpt v b θH θL x →
      buyerSurplusU v b θH θL x = 8 * v ^ 2 / Uden b θH θL ^ 2 ∧
      sellerSurplusU θH θH θL x = v ^ 2 * (2 * b + 3 * θH - θL) ^ 2 / (2 * Uden b θH θL ^ 2) ∧
      sellerSurplusU θL θH θL x = v ^ 2 * (2 * b + 3 * θL - θH) ^ 2 / (2 * Uden b θH θL ^ 2) ∧
      welfareU v b θH θL x =
        v ^ 2 * (24 - (2 * b + 3 * θH - θL) * (2 * b - θH + 3 * θL)) / Uden b θH θL ^ 2 := by sorry

end TwoSidedPD.Baseline
