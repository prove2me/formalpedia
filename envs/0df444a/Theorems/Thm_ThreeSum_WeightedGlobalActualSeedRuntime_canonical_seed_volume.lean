-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualSeedRuntime_canonical_seed_volume
-- name    : ThreeSum.WeightedGlobalActualSeedRuntime.canonical_seed_volume
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:16:44.609623+00:00
-- url     : https://prove2.me/theorems/9909c367-b887-4fd2-96f0-1cd5caf228ce
-- title:
--   Weighted Global Actual Seed Runtime: canonical seed volume
-- statement:
--   The literal seed score volume includes both source hash scans, the
--   complete requester DFS, the tensor output rows and the actual count host.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualSeedRuntime.lean#L108-L170
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualSeedRuntime.lean#L108-L170

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualPrefixRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaControllerCore
import Definitions.Def_Submission_Weighted_Global_TernarySeedCoefficientBudget
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixInit
import Definitions.Def_Submission_Weighted_Global_TernaryActualSeedRuntime
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSeed_seed

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

theorem ThreeSum.WeightedGlobalActualSeedRuntime.canonical_seed_volume {K k b m n j F carries seed : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs)
    (D : LightWeightedGlobalSeedScoreFactory.Data (config (nativePrime K m) j I A seed))
    (hK : 0<K) (hn : 1<n) (hFpos : 0<F)
    (hF : F≤(nativeFamily K m k).length)
    (hb : WeightedGlobalActualPrefixRuntime.localFactor m≤b) (hcarries : 1≤carries)
    (hB : I.nB≤n) (hC : I.nC≤n) (hrequest : I.requesterCount≤n*carries) :
    let host:=nativeHost (K:=K) (k:=k) j maps Q (sourceInput I A seed D)
    (seedVolume D host (4^fixedLength m) F (outputCap K k m F)
      (WeightedGlobalGoodOutputCatalog.raws maps (threshold K k m))
      (WeightedGlobalGoodOutputCatalog.wordCodes maps (threshold K k m))
      (WeightedGlobalGoodOutputCatalog.mapCodes maps (threshold K k m)):ℝ)≤
      (2*nativePrime K m+6:ℕ)*(carries:ℝ)*volumeBundle K k b m n j+(host.runtime:ℝ):= by sorry
