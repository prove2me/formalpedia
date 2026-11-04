-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualPrefixRuntime_wanted_native_count
-- name    : ThreeSum.WeightedGlobalActualPrefixRuntime.wanted_native_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:08:08.321382+00:00
-- url     : https://prove2.me/theorems/bb6a97a3-609e-4ff2-b956-8a88f666cb60
-- title:
--   Weighted Global Actual Prefix Runtime: wanted native count
-- statement:
--   The actual literal wanted count, with the complete physical requester
--   multiplicity (in particular 2^J) kept as an explicit factor.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualPrefixRuntime.lean#L525-L561
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualPrefixRuntime.lean#L525-L561

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

theorem ThreeSum.WeightedGlobalActualPrefixRuntime.wanted_native_count {K k b m n j F carries : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (I : Input)
    (hK : 0<K) (hgood : GoodBlock K m)
    (hF : F≤(nativeFamily K m k).length) (hb : localFactor m≤b)
    (hrequest : I.requesterCount≤n*carries) :
    let τ:=WeightedGlobalCoverCapParameters.rawThreshold (nativePrime K m)
      (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) k
    ((entries (r:=j) maps τ I).length:ℝ)≤
      (carries:ℝ)*(n:ℝ)*((nativePrime K m:ℝ)/(partitionCap m:ℝ))^j*(nativeFactor K k b m:ℝ)^j := by sorry
