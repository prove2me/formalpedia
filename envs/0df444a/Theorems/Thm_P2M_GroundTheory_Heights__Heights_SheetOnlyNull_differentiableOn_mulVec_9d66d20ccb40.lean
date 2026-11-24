-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetOnlyNull_differentiableOn_mulVec_9d66d20ccb40
-- name    : P2M_GroundTheory_Heights__Heights_SheetOnlyNull_differentiableOn_mulVec_9d66d20ccb40
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:05:36.53001+00:00
-- url     : https://prove2.me/theorems/f621b9d9-ace4-46a1-9416-325178526b73
-- title:
--   P2 M Ground Theory Heights  Heights Sheet Only Null differentiable On mul Vec 9d66d20ccb40: P2 M Ground Theory Heights  Heights Sheet Only Null differentiable On mul Vec 9d66d20ccb40
-- statement:
--   The P2 M Ground Theory Heights  Heights Sheet Only Null differentiable On mul Vec 9d66d20ccb40 construction uses the P2 M Ground Theory Heights  Heights Sheet Only Null differentiable On mul Vec 9d66d20ccb40 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetOnlyNull.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetOnlyNull.lean#L30-L33

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

theorem P2M_GroundTheory_Heights__Heights_SheetOnlyNull_differentiableOn_mulVec_9d66d20ccb40 {m : ℕ} (B : Matrix (Fin m) (Fin n) ℂ) {U : Set (Fin d → ℂ)}
    {s : (Fin d → ℂ) → Fin n → ℂ} (hs : DifferentiableOn ℂ s U) :
    DifferentiableOn ℂ (fun w => B *ᵥ s w) U := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SheetOnlyNull».«differentiableOn_mulVec» := P2M_GroundTheory_Heights__Heights_SheetOnlyNull_differentiableOn_mulVec_9d66d20ccb40
