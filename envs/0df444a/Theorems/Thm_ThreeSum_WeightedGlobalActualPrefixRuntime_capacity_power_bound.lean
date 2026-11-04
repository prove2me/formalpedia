-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualPrefixRuntime_capacity_power_bound
-- name    : ThreeSum.WeightedGlobalActualPrefixRuntime.capacity_power_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:08:26.584876+00:00
-- url     : https://prove2.me/theorems/8cec60da-ede3-46b4-917c-3f1e211f7538
-- title:
--   Weighted Global Actual Prefix Runtime: capacity power bound
-- statement:
--   Only the logarithm of the polynomial word envelope enters near-query
--   cost. No polynomial-size arena scan is inserted into the runtime bound.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualPrefixRuntime.lean#L844-L878
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualPrefixRuntime.lean#L844-L878

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

theorem ThreeSum.WeightedGlobalActualPrefixRuntime.capacity_power_bound {M n U κ D E : ℕ} (hM : 1<M) (hn : 1<n)
    (hU : U≤n^κ) :
    D*(n+U+1)^E+1≤2^(capacityBits M D E κ*(Nat.clog M (n^2)+1)) := by sorry
