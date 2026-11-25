-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_TraceConjugationCover_complexHessian_comp_holomorphic_matrix
-- name    : ReciprocityTheory.AnForm.A.TraceConjugationCover.complexHessian_comp_holomorphic_matrix
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:07:39.034808+00:00
-- url     : https://prove2.me/theorems/8c75f6a9-d3f6-46d0-bbf9-fb78dfb62f7d
-- title:
--   Trace Conjugation Cover: complex Hessian comp holomorphic matrix
-- statement:
--   The Trace Conjugation Cover construction uses the complex Hessian comp holomorphic matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ComplexHessianIsHermitianOfContDiffAt.lean#L162-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ComplexHessianIsHermitianOfContDiffAt.lean#L162-L170

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

theorem ReciprocityTheory.AnForm.A.TraceConjugationCover.complexHessian_comp_holomorphic_matrix (φ : (Fin E → ℂ) → ℝ) (τ : (Fin D → ℂ) → (Fin E → ℂ)) (z : Fin D → ℂ)
    (hτ : AnalyticAt ℂ τ z) (hφ : ContDiffAt ℝ 2 φ (τ z)) :
    hessC (φ ∘ τ) z = (Matrix.of fun a k => fderiv ℂ τ z (Pi.single k 1) a)ᵀ * hessC φ (τ z) *
      (Matrix.of fun a k => fderiv ℂ τ z (Pi.single k 1) a).map (starRingEnd ℂ) := by sorry
