-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ParamPieceInt_analyticAt_of_differentiableOn_516a147c42f5
-- name    : P2M_GroundTheory_Heights__Heights_ParamPieceInt_analyticAt_of_differentiableOn_516a147c42f5
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:58.380801+00:00
-- url     : https://prove2.me/theorems/0c5338fa-d433-4e91-86fb-9d4d16a0668f
-- title:
--   P2 M Ground Theory Heights  Heights Param Piece Int analytic At of differentiable On 516a147c42f5: P2 M Ground Theory Heights  Heights Param Piece Int analytic At of differentiable On 516a147c42f5
-- statement:
--   The P2 M Ground Theory Heights  Heights Param Piece Int analytic At of differentiable On 516a147c42f5 construction uses the P2 M Ground Theory Heights  Heights Param Piece Int analytic At of differentiable On 516a147c42f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PParamPieceInt.lean#L17-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PParamPieceInt.lean#L17-L28

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

theorem P2M_GroundTheory_Heights__Heights_ParamPieceInt_analyticAt_of_differentiableOn_516a147c42f5 {d m : ℕ} {U : Set (Fin d → ℂ)} {f : (Fin d → ℂ) → Fin m → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {x : Fin d → ℂ} (hx : x ∈ U) : AnalyticAt ℂ f x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ParamPieceInt».«analyticAt_of_differentiableOn» := P2M_GroundTheory_Heights__Heights_ParamPieceInt_analyticAt_of_differentiableOn_516a147c42f5
