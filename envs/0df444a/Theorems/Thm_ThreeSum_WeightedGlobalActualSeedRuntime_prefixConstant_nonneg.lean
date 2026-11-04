-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualSeedRuntime_prefixConstant_nonneg
-- name    : ThreeSum.WeightedGlobalActualSeedRuntime.prefixConstant_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:19:36.101356+00:00
-- url     : https://prove2.me/theorems/dd6a91f4-f4b2-43d1-9a90-4880e1efd2ad
-- title:
--   Weighted Global Actual Seed Runtime: prefix Constant nonneg
-- statement:
--   The Weighted Global Actual Seed Runtime construction uses the prefix Constant nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualSeedRuntime.lean#L696-L698
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualSeedRuntime.lean#L696-L698

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

theorem ThreeSum.WeightedGlobalActualSeedRuntime.prefixConstant_nonneg (K k c d m F D E κ B : ℕ) :
    0≤prefixConstant K k c d m F D E κ B:= by sorry
