-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualSeedRuntime_prepare_time_shape
-- name    : ThreeSum.WeightedGlobalActualSeedRuntime.prepare_time_shape
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:20:36.735968+00:00
-- url     : https://prove2.me/theorems/856e1793-240b-404d-8605-877f49035cbf
-- title:
--   Weighted Global Actual Seed Runtime: prepare time shape
-- statement:
--   The Weighted Global Actual Seed Runtime construction uses the prepare time shape property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualSeedRuntime.lean#L392-L410
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualSeedRuntime.lean#L392-L410

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

theorem ThreeSum.WeightedGlobalActualSeedRuntime.prepare_time_shape (m j alpha2 : ℕ) :
    LightWeightedGlobalPrefixPrepare.time m j alpha2≤
      10000*(fixedLength m+alpha2+1)*(j+2)*(WeightedGlobalDimensionBounds.bankSize m (j+1)+1):= by sorry
