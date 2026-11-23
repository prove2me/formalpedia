-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_det_restrictScalars_real
-- name    : ReciprocityTheory.AnForm.A.det_restrictScalars_real
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:16:59.756793+00:00
-- url     : https://prove2.me/theorems/f18fe8bf-60af-40e7-9f57-9e05081b6cc8
-- title:
--   A: det restrict Scalars real
-- statement:
--   The A construction uses the det restrict Scalars real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/LintegralImageEqLintegralNormSqDetMul.lean#L79-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/LintegralImageEqLintegralNormSqDetMul.lean#L79-L82

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

theorem ReciprocityTheory.AnForm.A.det_restrictScalars_real {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : V →ₗ[ℂ] V) :
    LinearMap.det (f.restrictScalars ℝ) = Complex.normSq (LinearMap.det f) := by sorry
