-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_TraceConjugationCover_lv_expand
-- name    : ReciprocityTheory.AnForm.A.TraceConjugationCover.lv_expand
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:05:48.126867+00:00
-- url     : https://prove2.me/theorems/8b05b175-668c-5129-b8e9-a61db929c423
-- title:
--   Trace Conjugation Cover: lv expand
-- statement:
--   The Trace Conjugation Cover construction uses the lv expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ComplexHessianIsHermitianOfContDiffAt.lean#L89-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ComplexHessianIsHermitianOfContDiffAt.lean#L89-L94

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

theorem ReciprocityTheory.AnForm.A.TraceConjugationCover.lv_expand (u v : Fin D → ℂ) :
    lv H u v = ∑ a, ∑ b, u a * lv H (Pi.single a 1) (Pi.single b 1) * starRingEnd ℂ (v b) := by sorry
