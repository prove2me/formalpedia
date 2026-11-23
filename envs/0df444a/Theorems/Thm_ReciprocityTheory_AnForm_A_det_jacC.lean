-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_det_jacC
-- name    : ReciprocityTheory.AnForm.A.det_jacC
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:04.971447+00:00
-- url     : https://prove2.me/theorems/4170fb96-e7ca-44ac-8b4b-efa7896e03a1
-- title:
--   A: det jac C
-- statement:
--   The A construction uses the det jac C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/LintegralImageEqLintegralNormSqDetMul.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/LintegralImageEqLintegralNormSqDetMul.lean#L33-L35

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

theorem ReciprocityTheory.AnForm.A.det_jacC (τ : (Fin D → ℂ) → (Fin D → ℂ)) (z : Fin D → ℂ) :
    (jacC τ z).det = LinearMap.det (fderiv ℂ τ z : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)) := by sorry
