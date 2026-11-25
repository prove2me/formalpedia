-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_TraceConjugationCover_lv_sum_right
-- name    : ReciprocityTheory.AnForm.A.TraceConjugationCover.lv_sum_right
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:05:40.0805+00:00
-- url     : https://prove2.me/theorems/98336cf5-e1ff-4bd6-bd36-9229d94544ba
-- title:
--   Trace Conjugation Cover: lv sum right
-- statement:
--   The Trace Conjugation Cover construction uses the lv sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ComplexHessianIsHermitianOfContDiffAt.lean#L76-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ComplexHessianIsHermitianOfContDiffAt.lean#L76-L87

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ComplexHessianIsHermitianOfContDiffAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.TraceConjugationCover
open Complex Filter Topology Matrix
noncomputable section
variable {D : ℕ} (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ)

theorem ReciprocityTheory.AnForm.A.TraceConjugationCover.lv_sum_right (a v : Fin D → ℂ) :
    lv H a v = ∑ i, starRingEnd ℂ (v i) * lv H a (Pi.single i 1) := by sorry
