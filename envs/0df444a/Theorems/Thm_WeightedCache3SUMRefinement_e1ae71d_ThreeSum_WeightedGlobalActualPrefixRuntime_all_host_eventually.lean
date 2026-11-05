-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalActualPrefixRuntime_all_host_eventually
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalActualPrefixRuntime.all_host_eventually
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T13:41:34.121422+00:00
-- url     : https://prove2.me/theorems/2fc0a012-f791-4005-9879-7252cb58785b
-- title:
--   all_host_eventually
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryActualPrefixRuntime.lean#L1011-L1074
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryActualPrefixRuntime.lean#L1011-L1074

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightTernarySourceHostBudget
import Definitions.Def_Submission_ThreeSum_TernaryWantedDictionaryFiber
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaQueryTime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizeDimensions
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentReporterBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernarySeedControllerBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernarySeedScoreFactory
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedPreparationBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryExtensionBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualPrefixRuntime
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalActualPrefixRuntime
open Light Real Filter Asymptotics
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend
open WeightedGlobalEntropyRates WeightedGlobalDimensionBounds WeightedGlobalOversizePrime
open WeightedGlobalOversizeRates WeightedGlobalOversizeOverhead WeightedGlobalCoverScale
open scoped BigOperators Topology
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalActualPrefixRuntime.all_host_eventually {K k b m κ F D E β : ℕ} {δ ε : ℝ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : ℕ→ℕ→Input) (U : ℕ→ℕ)
    (hK : 0<K) (hk : 0<k) (hgood : GoodBlock K m) (hβ : 1<β)
    (hU : ∀n, 1<n → U n≤n^κ) (hFpos : 0<F) (hF : F≤(nativeFamily K m k).length)
    (hb : localFactor m≤b)
    (hB : ∀n, 1<n → ∀j≤radixLength m n, (I n j).nB≤n)
    (hC : ∀n, 1<n → ∀j≤radixLength m n, (I n j).nC≤n)
    (hrequest : ∀n, 1<n → ∀j≤radixLength m n,
      (I n j).requesterCount≤n*2^WeightedGlobalSignedPadding.paddedLength β (U n) (radixLength m n))
    (hposL : 1≤(localRecords maps (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) false).length)
    (hposR : 1≤(localRecords maps (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) true).length)
    (hword : ∀n, 1<n → ∀j≤radixLength m n,
      WeightedGlobalFrontendResources.eulerBound (N m j)
        (valueCap (r:=j) maps (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) (I n j))≤D*(n+U n+1)^E)
    (htime : ∀n, 1<n → ∀j≤radixLength m n, (I n j).queryTime≤WeightedGlobalCountFrontendBudget.queryMax m j
      (nativeHost (K:=K) (k:=k) j maps Q (I n j)).front.f (nativeHost (K:=K) (k:=k) j maps Q (I n j)).front.g)
    (c d : ℕ) (hpoly : b≤c*(fixedLength m+1)^d)
    (hcarry : WeightedGlobalSignedPadding.carryExponent m β (κ:ℝ)<δ) (hε : 0<ε)
    (hgap : fullExponent K k c d m+δ+ε<WeightedGlobalParameters.targetExponent) :
    ∀ᶠ n : ℕ in atTop,
      (allHostTime (K:=K) (k:=k) maps Q (I n) n:ℝ)≤(n:ℝ)^WeightedGlobalParameters.targetExponent := by sorry
