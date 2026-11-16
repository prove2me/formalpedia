-- Prove2me | Theorems.Thm_SingleSampleCombPI_XOS_Supplement_lemma_5_6
-- name    : SingleSampleCombPI.XOS.Supplement.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:49:19.788165+00:00
-- url     : https://prove2.me/theorems/72c50a25-b5e5-449d-9656-8b29cccf61dd
-- title:
--   Lemma 5.6 — Residual-capacity lower bound away from every density
-- statement:
--   Fix the filled, distinct-density GoG experiment and $t\ge0$ unequal to every adversarial record's density. Let $M=\sum_i x(r_i)\mathbf1[\tau_s<q(r_i)\le t]$. Then
--   $$2\mathbb E[(1-M)^+\mathbf1[\tau_s<t]]\ge\Pr[\tau_s<t].$$
--   All sample/real orientation coins retain the dependent-pair GoG law; $a^+=\max\{0,a\}$.
--
--   Differences from the source:
--   - encoding: independent uniform sample and real quantiles conditional on orientations → quantileExp: fair GoG swaps followed by two separate uniform Lebesgue averages on [0,1]; reason: finite step functions are measurable and bounded; the two quantiles are not made unconditionally independent
--   - encoding: positive part of residual capacity → max 0 (1-mediumMass); reason: this is the real positive part, with no truncated natural-number subtraction
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), Lemma 5.6, printed p. 29 / PDF p. 31; proof printed 30 / PDF 32.

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Supplement_Knapsack

open scoped ENNReal

namespace SingleSampleCombPI.XOS.Supplement

/-- Lemma 5.6, PDF 31 / printed 29; proof PDF 32. No density equals t. -/
theorem lemma_5_6 {n : ℕ} (V : Fin n → Fin 2 → Item)
    (hV : FilledDistinct V) (t : ℝ) (ht : 0 ≤ t)
    (hne : ∀ i k, (V i k).1 ≠ t) :
    quantileExp V (fun _ _ τs _ => if τs < t then 1 else 0) ≤
      2 * quantileExp V (fun _ r τs _ =>
        if τs < t then max 0 (1 - mediumMass r τs t) else 0) := by sorry

end SingleSampleCombPI.XOS.Supplement
