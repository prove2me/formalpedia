-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_lintegral_image_eq_lintegral_normSq_det_mul
-- name    : ReciprocityTheory.AnForm.A.lintegral_image_eq_lintegral_normSq_det_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:36.022689+00:00
-- url     : https://prove2.me/theorems/fc7b22b7-f2ab-4f22-b9eb-93d31968cc3c
-- title:
--   A: lintegral image eq lintegral norm Sq det mul
-- statement:
--   The A construction uses the lintegral image eq lintegral norm Sq det mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/LintegralImageEqLintegralNormSqDetMul.lean#L105-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/LintegralImageEqLintegralNormSqDetMul.lean#L105-L118

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ComplexHessianIsHermitianOfContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_CovLog
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Matrix
noncomputable section
variable {D E : ℕ}

theorem ReciprocityTheory.AnForm.A.lintegral_image_eq_lintegral_normSq_det_mul (τ : (Fin D → ℂ) → (Fin D → ℂ))
    (U : Set (Fin D → ℂ)) (hU : IsOpen U) (hτ : AnalyticOnNhd ℂ τ U) (hinj : Set.InjOn τ U)
    (f : (Fin D → ℂ) → ENNReal) :
    ∫⁻ w in τ '' U, f w = ∫⁻ z in U, ENNReal.ofReal (Complex.normSq (jacC τ z).det) * f (τ z) := by sorry
