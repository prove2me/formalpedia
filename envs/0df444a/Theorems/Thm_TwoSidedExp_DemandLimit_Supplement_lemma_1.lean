-- Prove2me | Theorems.Thm_TwoSidedExp_DemandLimit_Supplement_lemma_1
-- name    : TwoSidedExp.DemandLimit.Supplement.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:21:54.61658+00:00
-- url     : https://prove2.me/theorems/acc09746-349d-419e-b150-561be2fdc2f3
-- title:
--   Lemma 1 (supports Theorem 2) — outside-option ratio bound
-- statement:
--   For real numbers A,B ≥ 0 and ϵ,ϵ′ > 0,
--
--   $$\left|\frac{A}{\epsilon+A+B}-\frac{A}{\epsilon'+A+B}\right|\le\frac{A}{\epsilon\epsilon'}|\epsilon-\epsilon'|.$$
--
--   This bounds the effect of perturbing the outside option in the mean-field approximation.
--
--   Differences from the source:
--   None.
-- source:
--   Johari, Li, Liskovich, Weintraub, Experimental Design in Two-Sided Platforms: An Analysis of Bias, arXiv:2002.05670v5, p. A4 (PDF 40), Lemma 1

import Mathlib
import Definitions.Def_TwoSidedExp_DemandLimit_Setting

open Filter Topology MeasureTheory

namespace TwoSidedExp.DemandLimit.Supplement

/-- Lemma 1, p. A4. -/
theorem lemma_1 (A B eps eps' : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (heps : 0 < eps) (heps' : 0 < eps') :
    |A / (eps + A + B) - A / (eps' + A + B)| ≤
      A / (eps * eps') * |eps - eps'| := by sorry

end TwoSidedExp.DemandLimit.Supplement
