-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalActualSeedRuntime_all_prefix_eventually
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalActualSeedRuntime.all_prefix_eventually
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:30:53.301411+00:00
-- url     : https://prove2.me/theorems/eb27d46b-536b-46cf-a43b-634538cf0b6c
-- title:
--   all_prefix_eventually
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryActualSeedRuntime.lean#L788-L851
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryActualSeedRuntime.lean#L788-L851

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualPrefixRuntime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaControllerCore
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySeedCoefficientBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixInit
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualSeedRuntime
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceSeed_seed
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCountFrontendBudget_all_prefix_eventually

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalActualSeedRuntime
open Real Light Filter
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalNativeCompleteFrontend
open WeightedGlobalActualPrefixRuntime WeightedGlobalEntropyRates WeightedGlobalOversizePrime
open WeightedGlobalOversizeRates WeightedGlobalOversizeOverhead WeightedGlobalCoverScale
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalActualSeedRuntime.all_prefix_eventually {K k b m κ F D0 E B β : ℕ} {δ ε : ℝ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : ℕ→ℕ→Input) (A : ℕ→Inputs) (U : ℕ→ℕ)
    (D : (n j seed : ℕ)→LightWeightedGlobalSeedScoreFactory.Data (config (nativePrime K m) j (I n j) (A n) seed))
    (hDB : ∀n,1<n→∀j≤radixLength m n,∀s,(D n j s).bB≤B)
    (hDC : ∀n,1<n→∀j≤radixLength m n,∀s,(D n j s).bC≤B)
    (hDO : ∀n,1<n→∀j≤radixLength m n,∀s,(D n j s).bO≤B)
    (hK : 0<K) (hk : 0<k) (hgood : GoodBlock K m) (hβ : 1<β)
    (hJ : ∀n,(A n).J=WeightedGlobalSignedPadding.paddedLength β (U n) (radixLength m n))
    (hU : ∀n,1<n→U n≤n^κ) (hFpos : 0<F) (hF : F≤(nativeFamily K m k).length)
    (hb : WeightedGlobalActualPrefixRuntime.localFactor m≤b)
    (hB : ∀n,1<n→∀j≤radixLength m n,(I n j).nB≤n)
    (hC : ∀n,1<n→∀j≤radixLength m n,(I n j).nC≤n)
    (hrequest : ∀n,1<n→∀j≤radixLength m n,(I n j).requesterCount≤n*2^(A n).J)
    (hposL : 1≤(localRecords maps (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) false).length)
    (hposR : 1≤(localRecords maps (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) true).length)
    (hword : ∀n,1<n→∀j≤radixLength m n,WeightedGlobalFrontendResources.eulerBound (N m j)
      (valueCap (r:=j) maps (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) (I n j))≤D0*(n+U n+1)^E)
    (htime : ∀n,1<n→∀j≤radixLength m n,(I n j).queryTime≤WeightedGlobalCountFrontendBudget.queryMax m j
      (nativeHost (K:=K) (k:=k) j maps Q (I n j)).front.f (nativeHost (K:=K) (k:=k) j maps Q (I n j)).front.g)
    (c d : ℕ) (hpoly : b≤c*(fixedLength m+1)^d)
    (hcarry : WeightedGlobalSignedPadding.carryExponent m β (κ:ℝ)<δ) (hε : 0<ε)
    (hgap : fullExponent K k c d m+δ+ε<WeightedGlobalParameters.targetExponent) :
    ∀ᶠ n : ℕ in atTop,
      (allPrefixTime (K:=K) (k:=k) maps Q (I n) (A n) (D n) n:ℝ)≤
        (n:ℝ)^WeightedGlobalParameters.targetExponent:= by sorry
