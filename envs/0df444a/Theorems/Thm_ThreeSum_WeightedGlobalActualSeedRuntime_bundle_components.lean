-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualSeedRuntime_bundle_components
-- name    : ThreeSum.WeightedGlobalActualSeedRuntime.bundle_components
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:16:15.910526+00:00
-- url     : https://prove2.me/theorems/a5621f33-e832-4338-9960-4699f0257e88
-- title:
--   Weighted Global Actual Seed Runtime: bundle components
-- statement:
--   Individual volumes needed by scalar hash scans, the span catalog and
--   literal requester DFS are all present in the charged native bundle.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualSeedRuntime.lean#L63-L95
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualSeedRuntime.lean#L63-L95

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

theorem ThreeSum.WeightedGlobalActualSeedRuntime.bundle_components {K k b m n j : ℕ} (hK : 0<K) (hn : 1<n)
    (hfactor : 1≤nativeFactor K k b m) :
    (n:ℝ)≤volumeBundle K k b m n j ∧
    ((nativePrime K m)^j:ℝ)≤volumeBundle K k b m n j ∧
    (nativeFactor K k b m:ℝ)^j*(n:ℝ)*((nativePrime K m:ℝ)/(partitionCap m:ℝ))^j≤volumeBundle K k b m n j ∧
    1≤volumeBundle K k b m n j := by sorry
