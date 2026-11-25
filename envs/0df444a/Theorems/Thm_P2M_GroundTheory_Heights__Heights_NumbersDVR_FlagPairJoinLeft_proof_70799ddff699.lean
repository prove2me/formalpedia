-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinLeft_proof_70799ddff699
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinLeft_proof_70799ddff699
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:33:26.488353+00:00
-- url     : https://prove2.me/theorems/728030f4-6e3f-4fa6-900d-bdcc4439c411
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Join Left proof 70799ddff699: P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Join Left proof 70799ddff699
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Join Left proof 70799ddff699 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Join Left proof 70799ddff699 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinFlagPairJoinLeft.lean#L283-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinFlagPairJoinLeft.lean#L283-L286

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisSide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerLast
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinFlagPairJoinLeft
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_joinCoord_assocVar_b75e0e1aca5e

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
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing div_mem_chartRing)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg joinCoord restrictChart chartMon IsGradedFrame IsUnitOn FlagPair IsPull
  IsVertDiv mcIdeal assocDeg assocVar joinCoord_assocVar)
open FlagPairJoinLeft

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinLeft_proof_70799ddff699 (hVert : JoinVerticalDivisorLeft.Statement) : FlagPairJoinLeft.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagPairJoinLeft».«proof» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinLeft_proof_70799ddff699
