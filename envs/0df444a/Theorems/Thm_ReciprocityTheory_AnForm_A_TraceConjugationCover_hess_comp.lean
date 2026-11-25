-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_TraceConjugationCover_hess_comp
-- name    : ReciprocityTheory.AnForm.A.TraceConjugationCover.hess_comp
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:06:46.479797+00:00
-- url     : https://prove2.me/theorems/67887473-e3b9-5503-a88e-7b422b8e4e6d
-- title:
--   Trace Conjugation Cover: hess comp
-- statement:
--   The Trace Conjugation Cover construction uses the hess comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ComplexHessianIsHermitianOfContDiffAt.lean#L102-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ComplexHessianIsHermitianOfContDiffAt.lean#L102-L141

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

theorem ReciprocityTheory.AnForm.A.TraceConjugationCover.hess_comp (φ : (Fin E → ℂ) → ℝ) (τ : (Fin D → ℂ) → (Fin E → ℂ))
    (z : Fin D → ℂ) (hτ : AnalyticAt ℂ τ z) (hφ : ContDiffAt ℝ 2 φ (τ z)) (w b : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ (φ ∘ τ)) z w b =
      fderiv ℝ (fderiv ℝ φ) (τ z) (fderiv ℂ τ z w) (fderiv ℂ τ z b) +
      fderiv ℝ φ (τ z) (fderiv ℂ (fun x => fderiv ℂ τ x b) z w) := by sorry
