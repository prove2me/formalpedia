-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_TraceConjugationCover_lv_comp
-- name    : ReciprocityTheory.AnForm.A.TraceConjugationCover.lv_comp
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:05:39.432389+00:00
-- url     : https://prove2.me/theorems/b1f2c340-508d-4560-8296-f3728569ade4
-- title:
--   Trace Conjugation Cover: lv comp
-- statement:
--   The Trace Conjugation Cover construction uses the lv comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ComplexHessianIsHermitianOfContDiffAt.lean#L143-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ComplexHessianIsHermitianOfContDiffAt.lean#L143-L160

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
variable {D E : ℕ}

theorem ReciprocityTheory.AnForm.A.TraceConjugationCover.lv_comp (φ : (Fin E → ℂ) → ℝ) (τ : (Fin D → ℂ) → (Fin E → ℂ))
    (z : Fin D → ℂ) (hτ : AnalyticAt ℂ τ z) (hφ : ContDiffAt ℝ 2 φ (τ z)) (a b : Fin D → ℂ) :
    lv (fderiv ℝ (fderiv ℝ (φ ∘ τ)) z) a b =
      lv (fderiv ℝ (fderiv ℝ φ) (τ z)) (fderiv ℂ τ z a) (fderiv ℂ τ z b) := by sorry
