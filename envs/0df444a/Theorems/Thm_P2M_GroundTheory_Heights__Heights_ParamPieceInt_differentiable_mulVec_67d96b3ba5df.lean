-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ParamPieceInt_differentiable_mulVec_67d96b3ba5df
-- name    : P2M_GroundTheory_Heights__Heights_ParamPieceInt_differentiable_mulVec_67d96b3ba5df
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:04.874796+00:00
-- url     : https://prove2.me/theorems/5795138e-3f44-4065-95a7-666384e0a9ba
-- title:
--   P2 M Ground Theory Heights  Heights Param Piece Int differentiable mul Vec 67d96b3ba5df: P2 M Ground Theory Heights  Heights Param Piece Int differentiable mul Vec 67d96b3ba5df
-- statement:
--   The P2 M Ground Theory Heights  Heights Param Piece Int differentiable mul Vec 67d96b3ba5df construction uses the P2 M Ground Theory Heights  Heights Param Piece Int differentiable mul Vec 67d96b3ba5df property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PParamPieceInt.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PParamPieceInt.lean#L32-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParamPieceInt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PParamPieceInt
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
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.ParamPieceInt
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ParamPieceInt_differentiable_mulVec_67d96b3ba5df (A : Matrix (Fin d) (Fin n) ℂ) :
    Differentiable ℂ (fun x : Fin n → ℂ => A *ᵥ x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ParamPieceInt».«differentiable_mulVec» := P2M_GroundTheory_Heights__Heights_ParamPieceInt_differentiable_mulVec_67d96b3ba5df
