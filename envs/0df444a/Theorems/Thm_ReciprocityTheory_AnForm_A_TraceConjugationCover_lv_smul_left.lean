-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_TraceConjugationCover_lv_smul_left
-- name    : ReciprocityTheory.AnForm.A.TraceConjugationCover.lv_smul_left
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:05:58.51581+00:00
-- url     : https://prove2.me/theorems/1d8374a5-f817-530d-bf21-1e5762d42a43
-- title:
--   Trace Conjugation Cover: lv smul left
-- statement:
--   The Trace Conjugation Cover construction uses the lv smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ComplexHessianIsHermitianOfContDiffAt.lean#L41-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ComplexHessianIsHermitianOfContDiffAt.lean#L41-L47

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

theorem ReciprocityTheory.AnForm.A.TraceConjugationCover.lv_smul_left (c : ℂ) (a b : Fin D → ℂ) : lv H (c • a) b = c * lv H a b := by sorry
