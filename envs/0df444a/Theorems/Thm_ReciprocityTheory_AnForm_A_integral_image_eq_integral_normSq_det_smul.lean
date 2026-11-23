-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_integral_image_eq_integral_normSq_det_smul
-- name    : ReciprocityTheory.AnForm.A.integral_image_eq_integral_normSq_det_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:44.195784+00:00
-- url     : https://prove2.me/theorems/3656cfde-117e-4491-9220-6f9966597590
-- title:
--   A: integral image eq integral norm Sq det smul
-- statement:
--   The A construction uses the integral image eq integral norm Sq det smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/LintegralImageEqLintegralNormSqDetMul.lean#L90-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/LintegralImageEqLintegralNormSqDetMul.lean#L90-L103

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

theorem ReciprocityTheory.AnForm.A.integral_image_eq_integral_normSq_det_smul {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (τ : (Fin D → ℂ) → (Fin D → ℂ)) (U : Set (Fin D → ℂ)) (hU : IsOpen U)
    (hτ : AnalyticOnNhd ℂ τ U) (hinj : Set.InjOn τ U) (f : (Fin D → ℂ) → F) :
    ∫ w in τ '' U, f w = ∫ z in U, Complex.normSq (jacC τ z).det • f (τ z) := by sorry
