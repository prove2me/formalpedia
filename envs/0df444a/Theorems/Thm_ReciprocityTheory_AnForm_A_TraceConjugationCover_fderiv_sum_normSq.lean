-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_TraceConjugationCover_fderiv_sum_normSq
-- name    : ReciprocityTheory.AnForm.A.TraceConjugationCover.fderiv_sum_normSq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:05:55.802925+00:00
-- url     : https://prove2.me/theorems/4e19faaa-055c-4be2-930f-611d94e1d6ab
-- title:
--   Trace Conjugation Cover: fderiv sum norm Sq
-- statement:
--   The Trace Conjugation Cover construction uses the fderiv sum norm Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ComplexHessianIsHermitianOfContDiffAt.lean#L214-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ComplexHessianIsHermitianOfContDiffAt.lean#L214-L228

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
variable {D : ℕ}

theorem ReciprocityTheory.AnForm.A.TraceConjugationCover.fderiv_sum_normSq :
    fderiv ℝ (fun w : Fin D → ℂ => ∑ i, Complex.normSq (w i)) =
      fun w => sqForm D w + (sqForm D).flip w := by sorry
