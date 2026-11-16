-- Prove2me | Theorems.Thm_SingleSampleCombPI_XOS_Supplement_lemma_5_4
-- name    : SingleSampleCombPI.XOS.Supplement.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:48:11.121196+00:00
-- url     : https://prove2.me/theorems/35ea0de6-b3f2-479c-b466-a542de9ad568
-- title:
--   Lemma 5.4 — Upper-tail joint symmetry in the filled distinct-density experiment
-- statement:
--   Fix the source filled, distinct-density GoG knapsack experiment and a threshold $t\ge0$. Write $\tau_s,\tau_r$ for the conditionally independent sample/real quantiles. Then the first term of the layer-cake comparison satisfies
--   $$2\mathbb E[K_r(\tau_s)\mathbf1[\tau_s\ge t]]=\Pr[\tau_s\ge t,\tau_r\ge t].$$
--   FilledDistinct includes the valid weights, filling and pairwise distinctness hypotheses stated before Observation 5.3.
--
--   Differences from the source:
--   - encoding: independent uniform sample and real quantiles conditional on orientations → quantileExp: fair GoG swaps followed by two separate uniform Lebesgue averages on [0,1]; reason: finite step functions are measurable and bounded; the two quantiles are not made unconditionally independent
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), Lemma 5.4, printed p. 29 / PDF p. 31; proof printed 29 / PDF 31.

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Supplement_Knapsack

open scoped ENNReal

namespace SingleSampleCombPI.XOS.Supplement

/-- Lemma 5.4, PDF 31 / printed 29. Quantiles are conditionally independent. -/
theorem lemma_5_4 {n : ℕ} (V : Fin n → Fin 2 → Item)
    (hV : FilledDistinct V) (t : ℝ) (ht : 0 ≤ t) :
    2 * quantileExp V (fun _ r τs _ => if t ≤ τs then knapTail r τs else 0) =
      quantileExp V (fun _ _ τs τr => if t ≤ τs ∧ t ≤ τr then 1 else 0) := by sorry

end SingleSampleCombPI.XOS.Supplement
