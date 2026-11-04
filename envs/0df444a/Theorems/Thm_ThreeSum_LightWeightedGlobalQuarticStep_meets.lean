-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalQuarticStep_meets
-- name    : ThreeSum.LightWeightedGlobalQuarticStep.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:02:52.477321+00:00
-- url     : https://prove2.me/theorems/9bc68b20-21f3-4968-85dc-fe2be9f079b9
-- title:
--   Light Weighted Global Quartic Step: meets
-- statement:
--   The Light Weighted Global Quartic Step construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryQuarticStep.lean#L20-L93
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryQuarticStep.lean#L20-L93

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorHeader
import Definitions.Def_Submission_Weighted_Global_LightTernaryQuarticStep
import Theorems.Thm_Light_MatAt_keep
import Theorems.Thm_Light_SegN_keep
import Theorems.Thm_Light_Seg_keep
import Theorems.Thm_Light_VecAt_keep
import Definitions.Def_WeightedCache3SUM_Alias_fe1d986d2522f297
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Theorems.Thm_ThreeSum_LightCacheEnumeration_meets
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Theorems.Thm_ThreeSum_LightFiniteTable_meets
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Definitions.Def_WeightedCache3SUM_Alias_eb65baeba73fd57c
import Definitions.Def_WeightedCache3SUM_Alias_3b3552e2795ab46d
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
import Theorems.Thm_ThreeSum_LightModuloCounts_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_03cdb09d18890d4e
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Definitions.Def_WeightedCache3SUM_Alias_375bd97fc128be02
import Definitions.Def_WeightedCache3SUM_Alias_54f2bf19dfb01d66
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_4b4040d8de1fb856
import Definitions.Def_WeightedCache3SUM_Alias_32e47c9a32bb047b
import Theorems.Thm_ThreeSum_LightReportingAffine_meets
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_meets
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Definitions.Def_WeightedCache3SUM_Alias_db7e3579c631dfa5
import Definitions.Def_WeightedCache3SUM_Alias_8c6e823b5fcef3e6
import Definitions.Def_WeightedCache3SUM_Alias_3b570d79c28763f9
import Definitions.Def_WeightedCache3SUM_Alias_075817043fa4e845
import Definitions.Def_WeightedCache3SUM_Alias_724c353a3aa82655
import Theorems.Thm_ThreeSum_LightSourceResidues_meets
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightTernaryDivide_meets
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerScan_meets
import Theorems.Thm_ThreeSum_LightTernaryGroupedSourceKeys_meets
import Theorems.Thm_ThreeSum_LightTernaryGroupedSources_meets
import Theorems.Thm_ThreeSum_LightTernaryInversePass_meets
import Theorems.Thm_ThreeSum_LightTernaryMetadata_meets
import Theorems.Thm_ThreeSum_LightTernaryPairedPolynomial_meets
import Theorems.Thm_ThreeSum_LightTernaryPairedPotentialBatch_meets
import Theorems.Thm_ThreeSum_LightTernaryPairedPotential_meets
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_LightTernaryProductChannel_meets
import Theorems.Thm_ThreeSum_LightTernaryProduct_meets
import Theorems.Thm_ThreeSum_LightTernaryQueryLookup_meets
import Theorems.Thm_ThreeSum_LightTernaryRankTable_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_meets
import Theorems.Thm_ThreeSum_LightTernarySignedRow_Procs_meets
import Theorems.Thm_ThreeSum_LightTernarySourceHistogram_meets
import Theorems.Thm_ThreeSum_LightTernarySourceKeys_meets
import Theorems.Thm_ThreeSum_LightTernaryTaggedChannel_meets
import Theorems.Thm_ThreeSum_LightTernaryTensorScatter_meets
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_meets
import Definitions.Def_WeightedCache3SUM_Alias_7018b9952430b957
import Definitions.Def_WeightedCache3SUM_Alias_5471e369d555e9e5
import Definitions.Def_WeightedCache3SUM_Alias_b5410f4bcc10d599
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_meets
import Theorems.Thm_ThreeSum_LightWeightedCost_meets
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_meets
import Theorems.Thm_ThreeSum_LightWeightedEulerMetadata_meets
import Theorems.Thm_ThreeSum_LightWeightedGroupBankStep_meets
import Theorems.Thm_ThreeSum_LightWeightedGroupedBanks_meets
import Theorems.Thm_ThreeSum_LightWeightedNearDigits_meets
import Theorems.Thm_ThreeSum_LightWeightedNearEnumerationMain_meets
import Theorems.Thm_ThreeSum_LightWeightedNearSourceWords_meets
import Theorems.Thm_ThreeSum_LightWeightedNearSource_meets
import Theorems.Thm_ThreeSum_LightWeightedPredecessorTable_meets
import Theorems.Thm_ThreeSum_LightWeightedPredecessor_meets
import Theorems.Thm_ThreeSum_LightWeightedPreparedState_Snapshot_meets
import Theorems.Thm_ThreeSum_LightWeightedWantedRowDispatch_meets
import Theorems.Thm_ThreeSum_ReportingHostRelocation_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalQuarticStep
open Light
set_option maxHeartbeats 2400000

theorem ThreeSum.LightWeightedGlobalQuarticStep.meets {lim : Limits} {P : Program}
    {pMain pChannel pOffset pProduct pCount pScatter d : ℕ}
    (config ls nL rs nR J wL wR tensor H countOut a b c e q W keep : ℕ)
    (μ : ℕ→ℤ) (L R : ℕ→ℕ→ℤ) (counts : ℕ→ℤ) (argv : List ℤ) (hostTime : ℕ)
    (hmain : P[pMain]?=some (body pChannel pCount pScatter))
    (hChannel : P[pChannel]?=some (LightTernaryTaggedChannel.body pOffset pProduct))
    (hOffset : P[pOffset]?=some LightTernaryTaggedChannel.offsetBody)
    (hProduct : P[pProduct]?=some LightTernaryProductChannel.body)
    (hScatter : P[pScatter]?=some LightTernaryTensorScatter.body)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+1<lim.depth)
    (ha : a<J+2) (hb : b<J+2) (hc : c<J+2) (he : e<J+2) (hq : q<W) (hW : 0<W)
    (hconfig : config+106≤wL) (hconfigSpace : config+106≤lim.space)
    (hls : ls+nL*(J+2)≤wL) (hrs : rs+nR*(J+2)≤wL)
    (hweights : wL+nL≤wR) (hweightsSpace : wR+nR≤lim.space)
    (htensor : tensor+H*W≤wL) (hkeep : wL≤keep)
    (hcount : countOut+H≤lim.space) (hcountSep : tensor+H*W≤countOut)
    (hWword : (W : ℤ)≤lim.word) (hHword : (H : ℤ)≤lim.word)
    (U : ℕ) (hword : ((U : ℤ)+1)^2≤lim.word) (hindex : ((J+3 : ℕ) : ℤ)≤lim.word)
    (hL : ∀ i<nL, ∀ j<J+2, μ (ls+i*(J+2)+TernarySignedLayout.offset J j)=L i j)
    (hR : ∀ i<nR, ∀ j<J+2, μ (rs+i*(J+2)+TernarySignedLayout.offset J j)=R i j)
    (hLb : ∀ i<nL, ∀ j<J+2, |L i j|≤(U : ℤ))
    (hRb : ∀ i<nR, ∀ j<J+2, |R i j|≤(U : ℤ))
    (hlen : argv.length=106) (hargs : ∀ i<106, μ (config+i)=argv.getD i 0)
    (hHost : ∀ ν, SameOutside2 μ ν wL nL wR nR →
      (∀ i<nL, ν (wL+i)=L i a*L i b) → (∀ i<nR, ν (wR+i)=R i c*R i e) →
      Meets lim P pCount (d+1) argv ν hostTime
        (fun _ ξ => Kept ν ξ keep ∧ ∀ j<H, ξ (countOut+j)=counts j)) :
    Meets lim P pMain d
      [config,ls,nL,rs,nR,J,wL,wR,tensor,H,countOut,a,b,c,e,q,W] μ
      (LightTernaryTaggedChannel.time nL+LightTernaryTaggedChannel.time nR+
        hostTime+LightTernaryTensorScatter.time H+1500)
      (fun _ ν => (∀ j<H, ν (tensor+j*W+q)=counts j) ∧
        ∀ x<wL, (∀ j<H, x≠tensor+j*W+q) → ν x=μ x) := by sorry
