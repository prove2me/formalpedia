-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualPrefixRuntime_canonical_host_prefix_bound
-- name    : ThreeSum.WeightedGlobalActualPrefixRuntime.canonical_host_prefix_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:07:38.671147+00:00
-- url     : https://prove2.me/theorems/d3906865-e09b-4fd8-8101-7ad9931c50e7
-- title:
--   Weighted Global Actual Prefix Runtime: canonical host prefix bound
-- statement:
--   Both actual source hosts and the actual count frontend are assembled
--   before the seed and moment drivers apply their fixed-dimensional loops.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualPrefixRuntime.lean#L748-L791
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualPrefixRuntime.lean#L748-L791

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

theorem ThreeSum.WeightedGlobalActualPrefixRuntime.canonical_host_prefix_bound {K k b m n j F carries : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (I : Input)
    (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (hK : 0<K) (hk : 0<k) (hgood : GoodBlock K m) (hn : 1<n)
    (hj : j≤radixLength m n) (hFpos : 0<F)
    (hF : F≤(nativeFamily K m k).length) (hb : localFactor m≤b)
    (hcarries : 1≤carries) (hrequest : I.requesterCount≤n*carries)
    (hB : I.nB≤n) (hC : I.nC≤n)
    (hposL : 1≤(localRecords maps (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) false).length)
    (hposR : 1≤(localRecords maps (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) true).length)
    (htime : I.queryTime≤WeightedGlobalCountFrontendBudget.queryMax m j
      (nearConfig (m:=m) (r:=j) I false
        (valueCap (r:=j) maps (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) I))
      (nearConfig (m:=m) (r:=j) I true
        (valueCap (r:=j) maps (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) I)))
    (c d : ℕ) (hpoly : b≤c*(fixedLength m+1)^d) :
    let τ:=WeightedGlobalCoverCapParameters.rawThreshold (nativePrime K m)
      (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) k
    let S:=setup (r:=j) maps τ (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) Q I
    (S.runtime:ℝ)≤
      (2*(8000*(2*fixedLength m+3*nativePrime K m+6)*(F*endpointSize m+3):ℕ)*(j+1:ℕ)+
        1000000*(WeightedGlobalCountFrontendBudget.width (N m j) S.front.f S.front.g:ℝ)^3*(carries:ℝ))*
        volumeConstant K k c d m*(n:ℝ)^fullExponent K k c d m := by sorry
