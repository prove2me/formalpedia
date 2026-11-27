-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ParamChartInt_proof_1ba5dd5dda3d
-- name    : P2M_GroundTheory_Heights__Heights_ParamChartInt_proof_1ba5dd5dda3d
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:34:21.070057+00:00
-- url     : https://prove2.me/theorems/186ce73b-d367-59cc-b3bb-f8d768f71c95
-- title:
--   P2 M Ground Theory Heights  Heights Param Chart Int proof 1ba5dd5dda3d: P2 M Ground Theory Heights  Heights Param Chart Int proof 1ba5dd5dda3d
-- statement:
--   The P2 M Ground Theory Heights  Heights Param Chart Int proof 1ba5dd5dda3d construction uses the P2 M Ground Theory Heights  Heights Param Chart Int proof 1ba5dd5dda3d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PParamChartInt.lean#L18-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PParamChartInt.lean#L18-L116

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParamChartInt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartIntCountAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParamPieceInt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParamCritNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParamOffRegularZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularInjectivePieces
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParamDensIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PParamChartInt
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

theorem P2M_GroundTheory_Heights__Heights_ParamChartInt_proof_1ba5dd5dda3d (hCA : ChartIntCountAdd.Statement) (hPI : ParamPieceInt.Statement)
    (hCN : ParamCritNull.Statement) (hOR : ParamOffRegularZero.Statement)
    (hRP : RegularInjectivePieces.Statement) (hDI : ParamDensIntegrable.Statement) :
    ParamChartInt.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ParamChartInt».«proof» := P2M_GroundTheory_Heights__Heights_ParamChartInt_proof_1ba5dd5dda3d
