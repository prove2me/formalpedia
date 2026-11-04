-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualPrefixRuntime_all_host_prefix_bound
-- name    : ThreeSum.WeightedGlobalActualPrefixRuntime.all_host_prefix_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:08:14.832634+00:00
-- url     : https://prove2.me/theorems/dda89937-99aa-4391-ad07-98207183cb8e
-- title:
--   Weighted Global Actual Prefix Runtime: all host prefix bound
-- statement:
--   Sum of the concrete source/count runtimes at every prefix. All bounds
--   are on original lengths, actual word magnitudes, and the literal typed
--   query maximum. The physical carry count is an explicit multiplier.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualPrefixRuntime.lean#L941-L1005
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualPrefixRuntime.lean#L941-L1005

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

theorem ThreeSum.WeightedGlobalActualPrefixRuntime.all_host_prefix_bound {K k b m n U κ F carries D E : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : ℕ→Input) (hK : 0<K) (hk : 0<k) (hgood : GoodBlock K m)
    (hn : 1<n) (hU : U≤n^κ) (hFpos : 0<F) (hF : F≤(nativeFamily K m k).length)
    (hb : localFactor m≤b) (hcarries : 1≤carries)
    (hB : ∀j≤radixLength m n, (I j).nB≤n) (hC : ∀j≤radixLength m n, (I j).nC≤n)
    (hrequest : ∀j≤radixLength m n, (I j).requesterCount≤n*carries)
    (hposL : 1≤(localRecords maps (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) false).length)
    (hposR : 1≤(localRecords maps (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) true).length)
    (hword : ∀j≤radixLength m n,
      WeightedGlobalFrontendResources.eulerBound (N m j)
        (valueCap (r:=j) maps (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) (I j))≤D*(n+U+1)^E)
    (htime : ∀j≤radixLength m n, (I j).queryTime≤WeightedGlobalCountFrontendBudget.queryMax m j
      (nativeHost (K:=K) (k:=k) j maps Q (I j)).front.f (nativeHost (K:=K) (k:=k) j maps Q (I j)).front.g)
    (c d : ℕ) (hpoly : b≤c*(fixedLength m+1)^d) :
    (allHostTime (K:=K) (k:=k) maps Q I n:ℝ)≤
      hostConstant K k c d m F D E κ*(radixLength m n+1:ℕ)^4*(carries:ℝ)*
        (n:ℝ)^fullExponent K k c d m := by sorry
