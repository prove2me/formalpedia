-- Prove2me | Theorems.Thm_PrefRobustSR_WorstCase_lemma_2_1_ii
-- name    : PrefRobustSR.WorstCase.lemma_2_1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:27.644972+00:00
-- url     : https://prove2.me/theorems/122dadb4-ec05-4d31-8671-470124c2fe25
-- title:
--   Lemma 2.1(ii), p. 5: loss functions diverge at +∞
-- statement:
--   For every loss function $l$ in the paper's class $\mathcal L$,
--   $$
--   \lim_{t\to+\infty}l(t)=+\infty.
--   $$
--   This property controls the shortfall constraint at very negative cash amounts and is used in (2.12).
-- source:
--   Delage, Guo & Xu, Shortfall risk models when information of loss function is incomplete, preprint dated April 25, 2018 (later article DOI: https://doi.org/10.1287/opre.2021.2212; numbering follows the preprint), p. 5, Lemma 2.1(ii); proof p. 43, Appendix A.1

import Mathlib
import Definitions.Def_PrefRobustSR_WorstCase_Model

namespace PrefRobustSR.WorstCase

open MeasureTheory

/-- Lemma 2.1(ii), p. 5: each member of 𝓛 tends to +∞. -/
theorem lemma_2_1_ii (l : ℝ → ℝ) (hl : l ∈ LossClass) :
    Filter.Tendsto l Filter.atTop Filter.atTop := by sorry

end PrefRobustSR.WorstCase
