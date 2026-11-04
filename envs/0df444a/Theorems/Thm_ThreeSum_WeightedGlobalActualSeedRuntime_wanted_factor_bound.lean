-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualSeedRuntime_wanted_factor_bound
-- name    : ThreeSum.WeightedGlobalActualSeedRuntime.wanted_factor_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:19:05.117468+00:00
-- url     : https://prove2.me/theorems/04880bd7-6be0-40ed-b737-77924c291043
-- title:
--   Weighted Global Actual Seed Runtime: wanted factor bound
-- statement:
--   The Weighted Global Actual Seed Runtime construction uses the wanted factor bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualSeedRuntime.lean#L30-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualSeedRuntime.lean#L30-L49

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

theorem ThreeSum.WeightedGlobalActualSeedRuntime.wanted_factor_bound {K k b m F : ℕ} (hK : 0<K)
    (hF : F≤(nativeFamily K m k).length) (hb : WeightedGlobalActualPrefixRuntime.localFactor m≤b) :
    (outputCap K k m F:ℝ)≤(nativeFactor K k b m:ℝ)*((nativePrime K m:ℝ)/(partitionCap m:ℝ)):= by sorry
