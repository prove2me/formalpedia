-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualPrefixRuntime_histogram_filter
-- name    : ThreeSum.WeightedGlobalActualPrefixRuntime.histogram_filter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:04:43.842612+00:00
-- url     : https://prove2.me/theorems/ee5bdb3d-6e63-45bf-8c7d-ca7a80ddd57d
-- title:
--   Weighted Global Actual Prefix Runtime: histogram filter
-- statement:
--   Every repeated key occurrence is counted. No injectivity of key values
--   is used to turn the physical histogram into a dictionary fiber.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualPrefixRuntime.lean#L35-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualPrefixRuntime.lean#L35-L53

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

theorem ThreeSum.WeightedGlobalActualPrefixRuntime.histogram_filter (xs : List ℤ) (f : ℤ→ℕ) (a : ℕ) :
    LightHistogram.count (fun j=>f (xs.getD j 0)) a xs.length=
      (xs.filter (fun z=>f z=a)).length := by sorry
