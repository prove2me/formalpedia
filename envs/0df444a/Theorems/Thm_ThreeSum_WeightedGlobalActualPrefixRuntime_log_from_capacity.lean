-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualPrefixRuntime_log_from_capacity
-- name    : ThreeSum.WeightedGlobalActualPrefixRuntime.log_from_capacity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:08:03.336586+00:00
-- url     : https://prove2.me/theorems/7fde7454-88a1-449b-b19f-f01279b42ecc
-- title:
--   Weighted Global Actual Prefix Runtime: log from capacity
-- statement:
--   The Weighted Global Actual Prefix Runtime construction uses the log from capacity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualPrefixRuntime.lean#L880-L884
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualPrefixRuntime.lean#L880-L884

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightTernarySourceHostBudget
import Definitions.Def_Submission_ThreeSum_TernaryWantedDictionaryFiber
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
import Definitions.Def_Submission_Weighted_Global_TernaryMomentReporterBudget
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedControllerBudget
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScoreFactory
import Definitions.Def_Submission_Weighted_Global_TernarySignedPreparationBudget
import Definitions.Def_Submission_Weighted_Global_TernaryExtensionBudget
import Definitions.Def_Submission_Weighted_Global_TernaryActualPrefixRuntime
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalActualPrefixRuntime
open Light Real Filter Asymptotics
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend
open WeightedGlobalEntropyRates WeightedGlobalDimensionBounds WeightedGlobalOversizePrime
open WeightedGlobalOversizeRates WeightedGlobalOversizeOverhead WeightedGlobalCoverScale
open scoped BigOperators Topology
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable

theorem ThreeSum.WeightedGlobalActualPrefixRuntime.log_from_capacity {M n U κ D E V : ℕ} (hM : 1<M) (hn : 1<n)
    (hU : U≤n^κ) (hV : V≤D*(n+U+1)^E) :
    Nat.log 2 (V+1)≤capacityBits M D E κ*(Nat.clog M (n^2)+1) := by sorry
