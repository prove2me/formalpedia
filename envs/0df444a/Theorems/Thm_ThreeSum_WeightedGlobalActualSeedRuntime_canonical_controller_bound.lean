-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalActualSeedRuntime_canonical_controller_bound
-- name    : ThreeSum.WeightedGlobalActualSeedRuntime.canonical_controller_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:20:45.214573+00:00
-- url     : https://prove2.me/theorems/63691a59-be2b-4328-a9e6-2f153d42dfa9
-- title:
--   Weighted Global Actual Seed Runtime: canonical controller bound
-- statement:
--   The Weighted Global Actual Seed Runtime construction uses the canonical controller bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualSeedRuntime.lean#L425-L502
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryActualSeedRuntime.lean#L425-L502

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

theorem ThreeSum.WeightedGlobalActualSeedRuntime.canonical_controller_bound {K k b m n U κ j F carries D0 E B : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs)
    (D : (seed : ℕ)→LightWeightedGlobalSeedScoreFactory.Data (config (nativePrime K m) j I A seed))
    (hDB : ∀s, (D s).bB≤B) (hDC : ∀s, (D s).bC≤B) (hDO : ∀s, (D s).bO≤B)
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
    (prefixControllerTime (K:=K) (k:=k) maps Q I A D:ℝ)≤
      controllerConstant K k c d m F D0 E κ B*
        (A.J+1:ℕ)^(seedPolynomialD K (nativePrime K m) B+5)*(carries:ℝ)*
          (n:ℝ)^fullExponent K k c d m:= by sorry
