-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LelongLimitOnZero_proof_2ceace49eeed
-- name    : P2M_GroundTheory_Heights__Heights_LelongLimitOnZero_proof_2ceace49eeed
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:03:09.240792+00:00
-- url     : https://prove2.me/theorems/adf7ce1c-5bdc-49c7-a424-58ae3f7d7c56
-- title:
--   P2 M Ground Theory Heights  Heights Lelong Limit On Zero proof 2ceace49eeed: P2 M Ground Theory Heights  Heights Lelong Limit On Zero proof 2ceace49eeed
-- statement:
--   The P2 M Ground Theory Heights  Heights Lelong Limit On Zero proof 2ceace49eeed construction uses the P2 M Ground Theory Heights  Heights Lelong Limit On Zero proof 2ceace49eeed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLelongLimitOnZero.lean#L100-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLelongLimitOnZero.lean#L100-L132

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongLimitOnZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongLimitOffZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongLimitGoodPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongMassNearSmall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarIntAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LocalLimitGlueOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongLimitOnZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LelongLimit_proof_0051504eefea

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets Function
open scoped ContDiff

theorem P2M_GroundTheory_Heights__Heights_LelongLimitOnZero_proof_2ceace49eeed (hOff : LelongLimitOffZero.Statement)
    (hGood : LelongLimitGoodPoints.Statement) (hSmall : LelongMassNearSmall.Statement)
    (hAdd : VarIntAdd.Statement) : LelongLimitOnZero.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LelongLimitOnZero».«proof» := P2M_GroundTheory_Heights__Heights_LelongLimitOnZero_proof_2ceace49eeed
