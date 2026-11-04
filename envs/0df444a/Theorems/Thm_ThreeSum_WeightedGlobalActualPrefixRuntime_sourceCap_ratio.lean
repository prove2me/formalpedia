-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualPrefixRuntime_sourceCap_ratio
-- name    : ThreeSum.WeightedGlobalActualPrefixRuntime.sourceCap_ratio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:05:26.082339+00:00
-- url     : https://prove2.me/theorems/11ea1112-2070-45b9-bb30-0754e330dfa6
-- title:
--   Weighted Global Actual Prefix Runtime: source Cap ratio
-- statement:
--   The trimmed endpoint bucket cap is paid by the already charged p/Rbar
--   incidence volume; seventeen is a fixed local multiplicity.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualPrefixRuntime.lean#L154-L182
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualPrefixRuntime.lean#L154-L182

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

theorem ThreeSum.WeightedGlobalActualPrefixRuntime.sourceCap_ratio {K m : ℕ} (hK : 0<K) (hgood : GoodBlock K m) :
    (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m):ℝ)≤
      17*(nativePrime K m:ℝ)/(partitionCap m:ℝ) := by sorry
