-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualSeedRuntime_prefix_init_shape
-- name    : ThreeSum.WeightedGlobalActualSeedRuntime.prefix_init_shape
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:21:05.487198+00:00
-- url     : https://prove2.me/theorems/92045a12-c672-4b88-b99d-72b0f84b4508
-- title:
--   Weighted Global Actual Seed Runtime: prefix init shape
-- statement:
--   The Weighted Global Actual Seed Runtime construction uses the prefix init shape property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualSeedRuntime.lean#L686-L691
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualSeedRuntime.lean#L686-L691

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualPrefixRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaControllerCore
import Definitions.Def_Submission_Weighted_Global_TernarySeedCoefficientBudget
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixInit
import Definitions.Def_Submission_Weighted_Global_TernaryActualSeedRuntime
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalActualSeedRuntime
open Real Light Filter
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalNativeCompleteFrontend
open WeightedGlobalActualPrefixRuntime WeightedGlobalEntropyRates WeightedGlobalOversizePrime
open WeightedGlobalOversizeRates WeightedGlobalOversizeOverhead WeightedGlobalCoverScale
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable

theorem ThreeSum.WeightedGlobalActualSeedRuntime.prefix_init_shape (C : LightWeightedGlobalSeedScoreFactory.Config) (rounds T : ℕ) :
    LightWeightedGlobalPrefixInit.time C rounds T≤
      (rounds+1)*(T+10000*(C.nB+C.nC+C.nO+C.J+1)):= by sorry
