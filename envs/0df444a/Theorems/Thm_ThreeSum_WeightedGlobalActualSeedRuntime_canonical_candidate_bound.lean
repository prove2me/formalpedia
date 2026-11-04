-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualSeedRuntime_canonical_candidate_bound
-- name    : ThreeSum.WeightedGlobalActualSeedRuntime.canonical_candidate_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:19:51.06974+00:00
-- url     : https://prove2.me/theorems/d6ce1983-0b31-441b-ac1c-dfdc190dbae0
-- title:
--   Weighted Global Actual Seed Runtime: canonical candidate bound
-- statement:
--   A concrete physical seed evaluation, including its complete signed
--   fourth-tensor construction, fits the same native dimension rates.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualSeedRuntime.lean#L187-L273
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualSeedRuntime.lean#L187-L273

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

theorem ThreeSum.WeightedGlobalActualSeedRuntime.canonical_candidate_bound {K k b m n U κ j F carries seed D0 E : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs)
    (D : LightWeightedGlobalSeedScoreFactory.Data (config (nativePrime K m) j I A seed))
    (B V : ℕ) (hDB : D.bB≤B) (hDC : D.bC≤B) (hDO : D.bO≤B)
    (hK : 0<K) (hk : 0<k) (hgood : GoodBlock K m) (hn : 1<n)
    (hj : j≤radixLength m n) (hJ : radixLength m n≤A.J) (hU : U≤n^κ)
    (hFpos : 0<F) (hF : F≤(nativeFamily K m k).length)
    (hb : WeightedGlobalActualPrefixRuntime.localFactor m≤b) (hcarries : 1≤carries)
    (hB : I.nB≤n) (hC : I.nC≤n) (hrequest : I.requesterCount≤n*carries)
    (hposL : 1≤(localRecords maps (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) false).length)
    (hposR : 1≤(localRecords maps (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) true).length)
    (hword : WeightedGlobalFrontendResources.eulerBound (N m j)
      (valueCap (r:=j) maps (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) I)≤D0*(n+U+1)^E)
    (htime : I.queryTime≤WeightedGlobalCountFrontendBudget.queryMax m j
      (nativeHost (K:=K) (k:=k) j maps Q I).front.f (nativeHost (K:=K) (k:=k) j maps Q I).front.g)
    (c d : ℕ) (hpoly : b≤c*(fixedLength m+1)^d) :
    let host:=nativeHost (K:=K) (k:=k) j maps Q (sourceInput I A seed D)
    (LightWeightedGlobalSeedScoreFactory.runtime D host K (4^fixedLength m) F (outputCap K k m F) V
      (WeightedGlobalGoodOutputCatalog.raws maps (threshold K k m))
      (WeightedGlobalGoodOutputCatalog.wordCodes maps (threshold K k m))
      (WeightedGlobalGoodOutputCatalog.mapCodes maps (threshold K k m)):ℝ)≤
      (seedCoefficient K A.J (nativePrime K m) B V j:ℝ)*scoreConstant K k c d m F D0 E κ*
        (A.J+1:ℕ)^3*(carries:ℝ)*(n:ℝ)^fullExponent K k c d m:= by sorry
