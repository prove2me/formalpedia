-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetOnlyNull_analyticOnNhd_det_jacC_ddf5e32b96d3
-- name    : P2M_GroundTheory_Heights__Heights_SheetOnlyNull_analyticOnNhd_det_jacC_ddf5e32b96d3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:54.949502+00:00
-- url     : https://prove2.me/theorems/23312434-b29e-4246-aa2d-ef97082dd1d4
-- title:
--   P2 M Ground Theory Heights  Heights Sheet Only Null analytic On Nhd det jac C ddf5e32b96d3: P2 M Ground Theory Heights  Heights Sheet Only Null analytic On Nhd det jac C ddf5e32b96d3
-- statement:
--   The P2 M Ground Theory Heights  Heights Sheet Only Null analytic On Nhd det jac C ddf5e32b96d3 construction uses the P2 M Ground Theory Heights  Heights Sheet Only Null analytic On Nhd det jac C ddf5e32b96d3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetOnlyNull.lean#L41-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetOnlyNull.lean#L41-L52

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetOnlyNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCriticalImageNull
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetOnlyNull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.SheetOnlyNull
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_SheetOnlyNull_analyticOnNhd_det_jacC_ddf5e32b96d3 {U : Set (Fin d → ℂ)} {F : (Fin d → ℂ) → Fin d → ℂ}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) :
    AnalyticOnNhd ℂ (fun w => (ReciprocityTheory.AnForm.A.jacC F w).det) U := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SheetOnlyNull».«analyticOnNhd_det_jacC» := P2M_GroundTheory_Heights__Heights_SheetOnlyNull_analyticOnNhd_det_jacC_ddf5e32b96d3
