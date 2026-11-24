-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_det_fderiv_real_eq_normSq
-- name    : ReciprocityTheory.AnForm.A.det_fderiv_real_eq_normSq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:00:54.453844+00:00
-- url     : https://prove2.me/theorems/c014673b-9657-4153-b425-acae54420ea1
-- title:
--   A: det fderiv real eq norm Sq
-- statement:
--   The A construction uses the det fderiv real eq norm Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/LintegralImageEqLintegralNormSqDetMul.lean#L84-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/LintegralImageEqLintegralNormSqDetMul.lean#L84-L88

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

theorem ReciprocityTheory.AnForm.A.det_fderiv_real_eq_normSq (τ : (Fin D → ℂ) → (Fin D → ℂ)) (z : Fin D → ℂ)
    (hτ : DifferentiableAt ℂ τ z) :
    (fderiv ℝ τ z).det = Complex.normSq (jacC τ z).det := by sorry
