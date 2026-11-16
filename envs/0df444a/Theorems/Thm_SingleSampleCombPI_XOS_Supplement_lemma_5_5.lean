-- Prove2me | Theorems.Thm_SingleSampleCombPI_XOS_Supplement_lemma_5_5
-- name    : SingleSampleCombPI.XOS.Supplement.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:48:36.614988+00:00
-- url     : https://prove2.me/theorems/0c87ace3-5e18-4776-b1d3-0ac1c1cda16c
-- title:
--   Lemma 5.5 — Lower-tail joint symmetry in the filled distinct-density experiment
-- statement:
--   In the same filled, distinct-density GoG experiment, for every $t\ge0$,
--   $$2\mathbb E[(1-K_r(\tau_s))\mathbf1[\tau_s<t]]=\Pr[\tau_s<t,\tau_r<t].$$
--   The expectation uses independent quantiles conditional on the buyer orientation coins.
--
--   Differences from the source:
--   - encoding: independent uniform sample and real quantiles conditional on orientations → quantileExp: fair GoG swaps followed by two separate uniform Lebesgue averages on [0,1]; reason: finite step functions are measurable and bounded; the two quantiles are not made unconditionally independent
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), Lemma 5.5, printed p. 29 / PDF p. 31; proof printed 29 / PDF 31.

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Supplement_Knapsack

open scoped ENNReal

namespace SingleSampleCombPI.XOS.Supplement

/-- Lemma 5.5, PDF 31 / printed 29, with the filled distinct-key preamble. -/
theorem lemma_5_5 {n : ℕ} (V : Fin n → Fin 2 → Item)
    (hV : FilledDistinct V) (t : ℝ) (ht : 0 ≤ t) :
    2 * quantileExp V (fun _ r τs _ => if τs < t then 1 - knapTail r τs else 0) =
      quantileExp V (fun _ _ τs τr => if τs < t ∧ τr < t then 1 else 0) := by sorry

end SingleSampleCombPI.XOS.Supplement
