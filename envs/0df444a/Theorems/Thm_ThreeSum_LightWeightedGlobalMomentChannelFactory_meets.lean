-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalMomentChannelFactory_meets
-- name    : ThreeSum.LightWeightedGlobalMomentChannelFactory.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:52:14.64404+00:00
-- url     : https://prove2.me/theorems/5582048a-e3bd-4fdb-95fa-f426e86bc2af
-- title:
--   Light Weighted Global Moment Channel Factory: meets
-- statement:
--   The Light Weighted Global Moment Channel Factory construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryMomentChannelFactory.lean#L42-L91
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryMomentChannelFactory.lean#L42-L91

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernarySourceCountWeightSeed
import Definitions.Def_Submission_Weighted_Global_LightTernaryMomentSourceProgram
import Definitions.Def_Submission_Weighted_Global_LightTernaryMomentChannelFactory
import Theorems.Thm_Light_SolvesN_meets
import Theorems.Thm_Light_Solves_meets
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
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Definitions.Def_WeightedCache3SUM_Alias_4b4040d8de1fb856
import Definitions.Def_WeightedCache3SUM_Alias_32e47c9a32bb047b
import Theorems.Thm_ThreeSum_LightReportingAffine_meets
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_meets
import Definitions.Def_WeightedCache3SUM_Alias_db7e3579c631dfa5
import Definitions.Def_WeightedCache3SUM_Alias_8c6e823b5fcef3e6
import Definitions.Def_WeightedCache3SUM_Alias_3b570d79c28763f9
import Definitions.Def_WeightedCache3SUM_Alias_075817043fa4e845
import Definitions.Def_WeightedCache3SUM_Alias_724c353a3aa82655
import Theorems.Thm_ThreeSum_LightSourceResidues_meets
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_meets
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_meets
import Theorems.Thm_ThreeSum_LightTernaryDivide_meets
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerMetadata_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerScan_meets
import Theorems.Thm_ThreeSum_LightTernaryGroupBankStep_meets
import Theorems.Thm_ThreeSum_LightTernaryGroupedBanks_meets
import Theorems.Thm_ThreeSum_LightTernaryGroupedSourceKeys_meets
import Theorems.Thm_ThreeSum_LightTernaryGroupedSources_meets
import Theorems.Thm_ThreeSum_LightTernaryInversePass_meets
import Theorems.Thm_ThreeSum_LightTernaryMetadata_meets
import Theorems.Thm_ThreeSum_LightTernaryMomentAccumulate_meets
import Theorems.Thm_ThreeSum_LightTernaryMomentChannelStep_Procs_meets
import Theorems.Thm_ThreeSum_LightTernaryNearDigits_meets
import Theorems.Thm_ThreeSum_LightTernaryNearEnumerationMain_meets
import Theorems.Thm_ThreeSum_LightTernaryNearSourceWords_meets
import Theorems.Thm_ThreeSum_LightTernaryNearSource_meets
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_LightTernaryPredecessorTable_meets
import Theorems.Thm_ThreeSum_LightTernaryPredecessor_meets
import Theorems.Thm_ThreeSum_LightTernaryPreparedState_Snapshot_meets
import Theorems.Thm_ThreeSum_LightTernaryProduct_meets
import Theorems.Thm_ThreeSum_LightTernaryQueryLookup_meets
import Theorems.Thm_ThreeSum_LightTernaryRankTable_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_meets
import Theorems.Thm_ThreeSum_LightTernaryScalarChannel_meets
import Theorems.Thm_ThreeSum_LightTernarySourceHistogram_meets
import Theorems.Thm_ThreeSum_LightTernarySourceKeys_meets
import Theorems.Thm_ThreeSum_LightTernaryWantedRowDispatch_meets
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_meets
import Definitions.Def_WeightedCache3SUM_Alias_7018b9952430b957
import Definitions.Def_WeightedCache3SUM_Alias_5471e369d555e9e5
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
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalMomentChannelFactory
open Light TernaryJointType TernaryWeightChannels

theorem ThreeSum.LightWeightedGlobalMomentChannelFactory.meets {lim : Limits} {N a b d originalB originalC matrix k j U V : ℕ}
    (S : WeightedSourceCountExecutionFactory.Setup N) (μ : ℕ→ℤ) (B C accum : ℕ→ℤ)
    (H : WeightedSourceCountExecutionFactory.Seed S lim (d+1) S.left.weightBase μ
      (leftWeights k j B) (rightWeights k j C))
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+1<lim.depth)
    (hBspace : originalB+S.left.NL≤S.left.weightBase)
    (hCspace : originalC+S.right.NL≤S.left.weightBase)
    (hmatrix : matrix+k*S.front.count+S.front.count≤S.left.weightBase)
    (hleft : S.left.weightBase+S.left.NL≤S.right.weightBase)
    (hright : S.right.weightBase+S.right.NL≤lim.space)
    (houtBefore : S.left.weightBase≤S.front.dst) (hout : S.front.dst+S.front.count≤lim.space)
    (hleftSpace : S.left.weightBase≤lim.space)
    (hB : ∀ i<S.left.NL, μ (originalB+i)=B i)
    (hC : ∀ i<S.right.NL, μ (originalC+i)=C i)
    (hBabs : ∀ i<S.left.NL, |B i|≤(U : ℤ)) (hCabs : ∀ i<S.right.NL, |C i|≤(U : ℤ))
    (haccum : ∀ i<S.front.count, μ (matrix+k*S.front.count+i)=accum i)
    (hbounded : ∀ i<S.front.count, |accum i|≤(V : ℤ) ∧ |score S B C k j i|≤(V : ℤ))
    (hleftWord : max (U : ℤ) (2*((k.choose j : ℤ)+1)*((U : ℤ)+2)^j)≤lim.word)
    (hrightWord : max (U : ℤ) (2*((U : ℤ)+1)^(k-j))≤lim.word)
    (haddWord : 2*(V : ℤ)≤lim.word) (hkWord : (k : ℤ)≤lim.word)
    (hargsWord : ∀ z∈args S originalB originalC matrix, |z|≤lim.word)
    (hleftHom : ∀ pair∈S.left.records, WeightedGlobalBank.rank (S.front.E.word (S.left.key pair.2))=a)
    (hrightHom : ∀ pair∈S.right.records, WeightedGlobalBank.rank (S.front.E.word (S.right.key pair.2))=b)
    (hQ : ∀ i<S.front.count, WeightedGlobalBank.rank (S.front.Q i)=a+b) :
    Meets lim (program S k j) 138 d (args S originalB originalC matrix) μ
      (LightTernaryMomentChannelStep.time k j S.left.NL S.right.NL S.front.count S.runtime 106)
      (fun r ν => r=0 ∧
        (∀ i<S.front.count, ν (matrix+k*S.front.count+i)=accum i+score S B C k j i) ∧
        ∀ x<S.left.weightBase,
          (x<matrix+k*S.front.count ∨ matrix+k*S.front.count+S.front.count≤x) → ν x=μ x) := by sorry
