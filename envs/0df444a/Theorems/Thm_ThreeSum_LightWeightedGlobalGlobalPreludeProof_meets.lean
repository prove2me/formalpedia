-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalGlobalPreludeProof_meets
-- name    : ThreeSum.LightWeightedGlobalGlobalPreludeProof.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:09:39.227719+00:00
-- url     : https://prove2.me/theorems/c9d26616-e224-4296-9d6e-6bd3b46af2e8
-- title:
--   Light Weighted Global Global Prelude Proof: meets
-- statement:
--   The entire once-per-input prelude is physically executed from [n,free].
--   Dimensions and the field menu are computed, never passed as input advice.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryGlobalPreludeProof.lean#L86-L278
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryGlobalPreludeProof.lean#L86-L278

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryGlobalPrelude
import Definitions.Def_Submission_Weighted_Global_LightTernaryGlobalPreludeProof
import Theorems.Thm_ThreeSum_LightArgumentTable_meets
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Theorems.Thm_ThreeSum_LightCacheEnumeration_meets
import Theorems.Thm_ThreeSum_LightCoefficientDecode_meets
import Theorems.Thm_ThreeSum_LightExtensionFactorCheck_Procs_meets
import Theorems.Thm_ThreeSum_LightExtensionFactorPredicate_Procs_meets
import Theorems.Thm_ThreeSum_LightExtensionMultiplyCell_meets
import Theorems.Thm_ThreeSum_LightExtensionMultiplyTable_meets
import Theorems.Thm_ThreeSum_LightExtensionQuotientPredicate_Procs_meets
import Theorems.Thm_ThreeSum_LightExtensionSeedMatrix_meets
import Theorems.Thm_ThreeSum_LightExtensionSeedRow_meets
import Theorems.Thm_ThreeSum_LightFiniteTable_meets
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d92129e9a4741fac
import Theorems.Thm_ThreeSum_LightNaturalDot_meets
import Definitions.Def_WeightedCache3SUM_Alias_54f2bf19dfb01d66
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Theorems.Thm_ThreeSum_LightPairSearch_meets
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_meets
import Theorems.Thm_ThreeSum_LightPolynomialProductArray_meets
import Theorems.Thm_ThreeSum_LightPolynomialProductCheck_meets
import Theorems.Thm_ThreeSum_LightPolynomialQuotientCheck_Procs_meets
import Theorems.Thm_ThreeSum_LightPrimeAddArray_meets
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Theorems.Thm_ThreeSum_LightScales_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_984013d7ba738e5d
import Theorems.Thm_ThreeSum_LightSignedCoefficientLayout_meets
import Theorems.Thm_ThreeSum_LightSignedCoefficientMatrix_meets
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightTernaryDivide_meets
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerScan_meets
import Theorems.Thm_ThreeSum_LightTernaryInversePass_meets
import Theorems.Thm_ThreeSum_LightTernaryMetadata_meets
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_LightTernaryProduct_meets
import Theorems.Thm_ThreeSum_LightTernaryQueryLookup_meets
import Theorems.Thm_ThreeSum_LightTernaryRankTable_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_meets
import Theorems.Thm_ThreeSum_LightTernaryRowSelector_meets
import Theorems.Thm_ThreeSum_LightTernarySignedRow_Procs_meets
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_meets
import Theorems.Thm_ThreeSum_LightWeightedCost_meets
import Theorems.Thm_ThreeSum_LightWeightedEulerMetadata_meets
import Theorems.Thm_ThreeSum_LightWeightedGlobalDigitLength_meets
import Theorems.Thm_ThreeSum_LightWeightedNearDigits_meets
import Theorems.Thm_ThreeSum_LightWeightedNearEnumerationMain_meets
import Theorems.Thm_ThreeSum_LightWeightedNearSourceWords_meets
import Theorems.Thm_ThreeSum_LightWeightedNearSource_meets
import Theorems.Thm_ThreeSum_LightWeightedPredecessorTable_meets
import Theorems.Thm_ThreeSum_LightWeightedPredecessor_meets
import Theorems.Thm_ThreeSum_ReportingHostRelocation_meets

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalGlobalPreludeProof
open Light LightWeightedGlobalGlobalPrelude
open LightExtensionBackendLayout hiding params
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedGlobalGlobalPreludeProof.meets {lim : Limits} {M b p K κ n free depth : ℕ} [Fact p.Prime]
    (μ : ℕ→ℤ) (hM : 1<M) (hb : 1<b) (hn : 0<n)
    (hw : (lim.space:ℤ)≤lim.word)
    (hspace : finish free (LightWeightedGlobalDimensions.dim M b p K n (n^κ)) p
      (p^(LightWeightedGlobalDimensions.dim M b p K n (n^κ))) (LightWeightedGlobalDimensions.J M b n (n^κ))≤lim.space)
    (hdepth : depth+15<lim.depth)
    (hScales : ((1000*(n+1):ℕ):ℤ)≤lim.word)
    (hDimensions : (LightWeightedGlobalDimensions.word M b p K n (n^κ):ℤ)≤lim.word)
    (hU : ((n^κ:ℕ):ℤ)≤lim.word) (hκ : (κ:ℤ)≤lim.word) :
    Meets lim (program M b p K κ) 49 depth [n,free] μ (time M b p K κ n free)
      (fun z ν=>∃c<p^(LightWeightedGlobalDimensions.dim M b p K n (n^κ)),
        z=(free:ℤ) ∧
        Irreducible (TernaryExtensionEncoding.monicOfCode (p:=p)
          (LightWeightedGlobalDimensions.dim M b p K n (n^κ)) c) ∧
        Seg ν free (header n (n^κ) (LightWeightedGlobalDimensions.r M n)
          (LightWeightedGlobalDimensions.J M b n (n^κ)) (LightWeightedGlobalDimensions.dim M b p K n (n^κ)) p
          (p^(LightWeightedGlobalDimensions.dim M b p K n (n^κ))) free c) ∧
        Seg ν (params free) (LightScales.values n) ∧
        Menu ν (backend free) (LightWeightedGlobalDimensions.dim M b p K n (n^κ)) p
          (p^(LightWeightedGlobalDimensions.dim M b p K n (n^κ))) (LightWeightedGlobalDimensions.J M b n (n^κ)) c ∧
        Kept μ ν free) := by sorry
