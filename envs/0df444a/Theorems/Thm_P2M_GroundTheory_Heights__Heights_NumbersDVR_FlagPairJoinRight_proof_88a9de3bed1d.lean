-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_proof_88a9de3bed1d
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_proof_88a9de3bed1d
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:32:40.059788+00:00
-- url     : https://prove2.me/theorems/5a282054-fbff-410d-88a7-bbc9a7831b33
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Join Right proof 88a9de3bed1d: P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Join Right proof 88a9de3bed1d
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Join Right proof 88a9de3bed1d construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Join Right proof 88a9de3bed1d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinFlagPairJoinRight.lean#L236-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinFlagPairJoinRight.lean#L236-L259

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsMoreAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinFlagPairJoinRight
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_joinCoord_midVar_3ed08dc9bce4

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
  midDeg midVar joinCoord_midVar)
open FlagPairJoinRight

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_proof_88a9de3bed1d (hVert : JoinVerticalDivisorRight.Statement) :
    FlagPairJoinRight.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagPairJoinRight».«proof» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_proof_88a9de3bed1d
