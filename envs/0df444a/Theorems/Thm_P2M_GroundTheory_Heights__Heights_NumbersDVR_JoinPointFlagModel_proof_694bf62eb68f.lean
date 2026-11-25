-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointFlagModel_proof_694bf62eb68f
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointFlagModel_proof_694bf62eb68f
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:36:02.615664+00:00
-- url     : https://prove2.me/theorems/2e80e326-52e1-500b-af18-58db70aa9381
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Point Flag Model proof 694bf62eb68f: P2 M Ground Theory Heights  Heights Numbers DVR Join Point Flag Model proof 694bf62eb68f
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Point Flag Model proof 694bf62eb68f construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Point Flag Model proof 694bf62eb68f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinPointFlagModel.lean#L194-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinPointFlagModel.lean#L194-L211

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerExtra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinJoinPointFlagModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg joinCoord restrictChart pullDeg liftVar ptIdx ptCoord chartMon
  IsGradedFrame IsUnitOn FlagPair IsPull fnField IsVertDiv mcIdeal)
open JoinPointFlagModel

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointFlagModel_proof_694bf62eb68f (hIff : FlagPairCharacterisation.Statement.{0, 0, 0})
    (hModel : JoinPointModel.Statement) (hVert : JoinPointVerticalDivisor.Statement) :
    JoinPointFlagModel.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinPointFlagModel».«proof» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointFlagModel_proof_694bf62eb68f
