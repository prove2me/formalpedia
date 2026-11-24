-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetOnlyNull_injective_iff_det_ne_zero_4dda9d931b27
-- name    : P2M_GroundTheory_Heights__Heights_SheetOnlyNull_injective_iff_det_ne_zero_4dda9d931b27
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:14.008665+00:00
-- url     : https://prove2.me/theorems/1bd716df-1410-46e3-b3c0-c2ae78f42f16
-- title:
--   P2 M Ground Theory Heights  Heights Sheet Only Null injective iff det ne zero 4dda9d931b27: P2 M Ground Theory Heights  Heights Sheet Only Null injective iff det ne zero 4dda9d931b27
-- statement:
--   The P2 M Ground Theory Heights  Heights Sheet Only Null injective iff det ne zero 4dda9d931b27 construction uses the P2 M Ground Theory Heights  Heights Sheet Only Null injective iff det ne zero 4dda9d931b27 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetOnlyNull.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetOnlyNull.lean#L20-L24

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

theorem P2M_GroundTheory_Heights__Heights_SheetOnlyNull_injective_iff_det_ne_zero_4dda9d931b27 (L : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) :
    Function.Injective L ↔ LinearMap.det (L : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SheetOnlyNull».«injective_iff_det_ne_zero» := P2M_GroundTheory_Heights__Heights_SheetOnlyNull_injective_iff_det_ne_zero_4dda9d931b27
