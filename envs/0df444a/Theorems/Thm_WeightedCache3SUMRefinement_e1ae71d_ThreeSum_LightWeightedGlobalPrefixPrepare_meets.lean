-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalPrefixPrepare_meets
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixPrepare.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T14:32:07.668244+00:00
-- url     : https://prove2.me/theorems/61e92ffa-2efb-4e35-9085-c3083bd57e4b
-- title:
--   meets
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryPrefixPrepare.lean#L43-L150
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryPrefixPrepare.lean#L43-L150

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPrefixHeaderSegment
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPrefixSetupResources
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixPrepare
import Theorems.Thm_Light_SolvesN_meets
import Theorems.Thm_Light_Solves_meets
import Definitions.Def_WeightedCache3SUM_Alias_fe1d986d2522f297
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
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
import Definitions.Def_WeightedCache3SUM_Alias_d92129e9a4741fac
import Theorems.Thm_ThreeSum_LightNaturalDot_meets
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
import Theorems.Thm_ThreeSum_LightSignedRowHash_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Definitions.Def_WeightedCache3SUM_Alias_db7e3579c631dfa5
import Definitions.Def_WeightedCache3SUM_Alias_8c6e823b5fcef3e6
import Definitions.Def_WeightedCache3SUM_Alias_3b570d79c28763f9
import Definitions.Def_WeightedCache3SUM_Alias_075817043fa4e845
import Definitions.Def_WeightedCache3SUM_Alias_724c353a3aa82655
import Theorems.Thm_ThreeSum_LightSourceResidues_meets
import Theorems.Thm_ThreeSum_LightSpanAxpy_meets
import Theorems.Thm_ThreeSum_LightSpanCatalogBlock_meets
import Theorems.Thm_ThreeSum_LightSpanCatalogStep_meets
import Theorems.Thm_ThreeSum_LightSpanCatalogTest_meets
import Theorems.Thm_ThreeSum_LightSpanRowEqual_meets
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightTernaryAppendKeys_Procs_meets
import Theorems.Thm_ThreeSum_LightTernaryBudgetStep_meets
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
import Theorems.Thm_ThreeSum_LightTernaryRepeatWord_meets
import Theorems.Thm_ThreeSum_LightTernaryRowSelector_meets
import Theorems.Thm_ThreeSum_LightTernarySignedRow_Procs_meets
import Theorems.Thm_ThreeSum_LightTernarySourceHistogram_meets
import Theorems.Thm_ThreeSum_LightTernarySourceKeys_meets
import Theorems.Thm_ThreeSum_LightTernaryTaggedChannel_meets
import Theorems.Thm_ThreeSum_LightTernaryTensorScatter_meets
import Theorems.Thm_ThreeSum_LightTernaryWantedCanonical_meets
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_meets
import Definitions.Def_WeightedCache3SUM_Alias_7018b9952430b957
import Definitions.Def_WeightedCache3SUM_Alias_5471e369d555e9e5
import Definitions.Def_WeightedCache3SUM_Alias_b5410f4bcc10d599
import Theorems.Thm_ThreeSum_ReportingHostRelocation_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedBankAssembly_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCost_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_main
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedEnumerationSetup_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedEulerMetadata_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalPrefixHeader_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalPrefixSetup_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalQuarticStep_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGroupBankStep_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGroupedBanks_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearDigits_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearEnumerationMain_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearSourceWords_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearSource_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPredecessorTable_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPredecessor_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedPreparedState_Snapshot_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedWantedRowDispatch_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPrefixSetupResources_meets
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.main


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixPrepare
open Light LightWeightedGlobalPrefixLoop
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixPrepare.meets {lim : Limits} {P : Program}
    {main m F p liveSeed template liveHeader prefixFree alpha2 alphaRank localQ radix J a b scale j power
      Fbase Gbase xB xC xP tB tC tP d : ℕ}
    (hmain : P[main]?=some prepareBody)
    (hpAllocate : P[184]?=some (LightWeightedGlobalPrefixSetup.allocateBody 180 179))
    (hpPrefix : P[179]?=some (LightWeightedGlobalPrefixSetup.body 180 181))
    (hpPower : P[180]?=some LightNatPower.body)
    (hpSetup : P[181]?=some (LightWeightedEnumerationSetup.body 182 183))
    (hpPowers : P[182]?=some powTableBody)
    (hpEnum : P[183]?=some (LightCacheEnumeration.body 183))
    (hpHeader : P[191]?=some headerBody) (hpCopy : P[189]?=some copyBody)
    (hpRepeat : P[190]?=some LightTernaryRepeatWord.body)
    (hpBudget : P[195]?=some LightTernaryBudgetStep.body)
    (μ : ℕ→ℤ) (hw : (lim.space:ℤ)≤lim.word)
    (hprefixSpace : LightWeightedGlobalPrefixSetup.endAt prefixFree m (j+1)≤lim.space)
    (hprefixWord : (LightWeightedGlobalPrefixSetup.word m (j+1) F:ℤ)≤lim.word)
    (hdepth : d+LightWeightedGlobalPrefixSetup.N m (j+1)+5≤lim.depth)
    (hj : ((j+1:ℕ):ℤ)≤lim.word)
    (htemplate : template+106≤liveHeader) (hheader : liveHeader+106≤liveSeed)
    (hseed : liveSeed+48≤prefixFree)
    (hF : μ (template+99)=(Fbase:ℤ)) (hG : μ (template+100)=(Gbase:ℤ))
    (hD : LightWeightedGlobalPrefixSetup.T m (j+1)+2739≤(2738*(alphaRank*(j+1))+6*(alpha2*(j+1))))
    (hN1 : (LightWeightedGlobalPrefixSetup.N m (j+1):ℤ)+1≤lim.word)
    (hfits : ∀x∈(LightWeightedGlobalPrefixHeader.args template liveHeader
      (LightWeightedGlobalPrefixSetup.headerAt prefixFree m (j+1)) (j+1) m p power alpha2 alphaRank localQ radix J++
      LightWeightedGlobalPrefixHeader.locals (LightWeightedGlobalPrefixSetup.N m (j+1))
        (LightWeightedGlobalPrefixSetup.T m (j+1)) (2*LightWeightedGlobalPrefixSetup.N m (j+1))
        (F^(j+1)) (LightWeightedGlobalPrefixSetup.nb m (j+1)) prefixFree
        (LightWeightedGlobalPrefixSetup.workAt prefixFree m (j+1)) (j+1) p power alpha2 alphaRank localQ radix Fbase Gbase),
      |x|≤lim.word)
    (hpower : ∀i≤alpha2*(j+1), ((2^i:ℕ):ℤ)≤lim.word)
    (hquery : ∀i≤j+1, (LightTernaryRepeatWord.value localQ radix i:ℤ)≤lim.word)
    (hbudget : Seg μ (liveSeed+41) (LightTernaryBudgetStep.oldValues xB xC xP tB tC tP))
    (hnext : ∀x∈LightTernaryBudgetStep.nextValues p a b scale xB xC xP tB tC tP, x≤lim.word)
    (hmid : ((tP*b:ℕ):ℤ)≤lim.word) (h9 : (9:ℤ)≤lim.word) :
    Meets lim P main d (stepArgs m F p liveSeed template liveHeader prefixFree alpha2 alphaRank localQ radix J a b scale j power)
      μ (time m j alpha2)
      (fun r ν=>r=((power*p:ℕ):ℤ) ∧ ∃ μ₁ μ₂,
        Seg μ₁ (LightWeightedGlobalPrefixSetup.headerAt prefixFree m (j+1))
          (LightWeightedGlobalPrefixSetup.header m (j+1) F prefixFree (LightWeightedGlobalPrefixSetup.workAt prefixFree m (j+1))) ∧
        Seg μ₁ prefixFree ((WeightedAddresses.codes (LightWeightedGlobalPrefixSetup.N m (j+1))
          (LightWeightedGlobalPrefixSetup.T m (j+1))).map (fun (c:ℕ)=>(c:ℤ))) ∧
        LightSubsetAddress.Powers μ₁ (LightWeightedGlobalPrefixSetup.workAt prefixFree m (j+1))
          (2*LightWeightedGlobalPrefixSetup.N m (j+1)) ∧ Kept μ μ₁ prefixFree ∧
        HeaderReceipt μ₁ μ₂ m F p template liveHeader prefixFree alpha2 alphaRank localQ radix J j power Fbase Gbase ∧
        SameOutside μ₁ μ₂ liveHeader 106 ∧
        ν=LightTernaryBudgetStep.changed (seedChanged μ₂ liveSeed power liveHeader (j+1))
          (liveSeed+41) p a b scale xB xC xP tB tC tP) := by sorry
