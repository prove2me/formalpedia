-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualPrefixRuntime_volume_bundle_bound
-- name    : ThreeSum.WeightedGlobalActualPrefixRuntime.volume_bundle_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:05:18.823958+00:00
-- url     : https://prove2.me/theorems/64a219fe-2433-4ecf-a1ba-b226b5ef3796
-- title:
--   Weighted Global Actual Prefix Runtime: volume bundle bound
-- statement:
--   The Weighted Global Actual Prefix Runtime construction uses the volume bundle bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualPrefixRuntime.lean#L264-L331
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualPrefixRuntime.lean#L264-L331

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

theorem ThreeSum.WeightedGlobalActualPrefixRuntime.volume_bundle_bound {K k b m n j : ℕ}
    (hK : 0<K) (hk : 0<k) (hm : 0<m) (hn : 1<n)
    (hj : j≤radixLength m n) (c d : ℕ) (hb : b≤c*(fixedLength m+1)^d) :
    volumeBundle K k b m n j≤volumeConstant K k c d m*(n:ℝ)^fullExponent K k c d m := by sorry
