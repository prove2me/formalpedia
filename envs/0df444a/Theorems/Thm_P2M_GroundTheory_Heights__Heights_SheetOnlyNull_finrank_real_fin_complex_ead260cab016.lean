-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetOnlyNull_finrank_real_fin_complex_ead260cab016
-- name    : P2M_GroundTheory_Heights__Heights_SheetOnlyNull_finrank_real_fin_complex_ead260cab016
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:19.247778+00:00
-- url     : https://prove2.me/theorems/80c341c8-2208-4d66-a32a-619d50ce0cff
-- title:
--   P2 M Ground Theory Heights  Heights Sheet Only Null finrank real fin complex ead260cab016: P2 M Ground Theory Heights  Heights Sheet Only Null finrank real fin complex ead260cab016
-- statement:
--   The P2 M Ground Theory Heights  Heights Sheet Only Null finrank real fin complex ead260cab016 construction uses the P2 M Ground Theory Heights  Heights Sheet Only Null finrank real fin complex ead260cab016 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetOnlyNull.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetOnlyNull.lean#L26-L28

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

theorem P2M_GroundTheory_Heights__Heights_SheetOnlyNull_finrank_real_fin_complex_ead260cab016 (d : ℕ) : Module.finrank ℝ (Fin d → ℂ) = 2 * d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SheetOnlyNull».«finrank_real_fin_complex» := P2M_GroundTheory_Heights__Heights_SheetOnlyNull_finrank_real_fin_complex_ead260cab016
