-- Prove2me | Theorems.Thm_ThreeSum_LightSharedReportingBank_program_meets_w3sum_ac885d1
-- name    : ThreeSum.LightSharedReportingBank.program_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T19:04:42.979493+00:00
-- url     : https://prove2.me/theorems/26d57667-988f-4876-b59b-d3ce61e39bca
-- title:
--   Light Shared Reporting Bank: program meets
-- statement:
--   The Light Shared Reporting Bank construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSharedReportingBank.lean#L64-L200
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSharedReportingBank.lean#L64-L200

import Definitions.Def_Submission_ThreeSum_LightSharedReportingPair
import Definitions.Def_Submission_ThreeSum_SharedReportingBankRows
import Definitions.Def_Submission_ThreeSum_LightSharedReportingBank
import Theorems.Thm_ThreeSum_LightBandEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Theorems.Thm_ThreeSum_LightBlockBoxes_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_427f455cbe093cd3
import Theorems.Thm_ThreeSum_LightBlockChildren_program_meets
import Theorems.Thm_ThreeSum_LightBlockCoefficients_program_meets
import Theorems.Thm_ThreeSum_LightBlockQuery_program_meets
import Theorems.Thm_ThreeSum_LightBlockSourceHashes_program_meets
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Theorems.Thm_ThreeSum_LightBoxStages_program_meets
import Theorems.Thm_ThreeSum_LightBoxSum_program_meets
import Theorems.Thm_ThreeSum_LightCanonicalBoxSum_program_meets
import Theorems.Thm_ThreeSum_LightCapacity_program_meets
import Theorems.Thm_ThreeSum_LightCoverGreedy_program_meets
import Theorems.Thm_ThreeSum_LightCoverScores_program_meets
import Theorems.Thm_ThreeSum_LightCoverSelect_program_meets
import Theorems.Thm_ThreeSum_LightCoverUpdate_program_meets
import Theorems.Thm_ThreeSum_LightCyclic_program_meets
import Theorems.Thm_ThreeSum_LightDownsetAddress_program_meets
import Theorems.Thm_ThreeSum_LightDownsetEnumerationSetup_program_meets
import Theorems.Thm_ThreeSum_LightDownsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightDownsetSize_program_meets
import Theorems.Thm_ThreeSum_LightExplicitSum_program_meets
import Theorems.Thm_ThreeSum_LightKaratsuba_program_meets
import Theorems.Thm_ThreeSum_LightLeafSum_program_meets
import Theorems.Thm_ThreeSum_LightLocalCoverSchedule_program_meets
import Theorems.Thm_ThreeSum_LightLookupSum_program_meets
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightMaskHashes_program_meets
import Theorems.Thm_ThreeSum_LightMaskMinimum_program_meets
import Theorems.Thm_ThreeSum_LightMaskUnion_program_meets
import Theorems.Thm_ThreeSum_LightModuloCounts_program_meets
import Theorems.Thm_ThreeSum_LightOneHot_program_meets
import Theorems.Thm_ThreeSum_LightOutputDecodeDigits_program_meets
import Theorems.Thm_ThreeSum_LightOutputDecodeDivide_program_meets
import Theorems.Thm_ThreeSum_LightPairFlags_program_meets
import Theorems.Thm_ThreeSum_LightPrimeChain_program_meets
import Theorems.Thm_ThreeSum_LightPrimeMinimum_program_meets
import Theorems.Thm_ThreeSum_LightQueryBox_program_meets
import Theorems.Thm_ThreeSum_LightQueryEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightQueryWeights_program_meets
import Theorems.Thm_ThreeSum_LightRadixDigit_program_meets
import Theorems.Thm_ThreeSum_LightRadixKeys_program_meets
import Theorems.Thm_ThreeSum_LightRadixRows_program_meets
import Theorems.Thm_ThreeSum_LightReportingAffine_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_a2917ec7b7f9f23f
import Definitions.Def_WeightedCache3SUM_Alias_fc697fae61d94ff7
import Definitions.Def_WeightedCache3SUM_Alias_bb907f0b533f0452
import Definitions.Def_WeightedCache3SUM_Alias_fb2417efddae0cb5
import Definitions.Def_WeightedCache3SUM_Alias_7f1c96094f5b1c13
import Definitions.Def_WeightedCache3SUM_Alias_00b35c3259394183
import Theorems.Thm_ThreeSum_LightReportingFilter_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_0d2857ef7f97fcc6
import Definitions.Def_WeightedCache3SUM_Alias_781f7abf8592a079
import Theorems.Thm_ThreeSum_LightReportingGather_program_meets
import Theorems.Thm_ThreeSum_LightReportingPackKeys_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_8a2cd73670b38080
import Definitions.Def_WeightedCache3SUM_Alias_bfa505cca5c6af3f
import Definitions.Def_WeightedCache3SUM_Alias_9e2aececf85d8818
import Definitions.Def_WeightedCache3SUM_Alias_f4a3749c14d0f5f9
import Definitions.Def_WeightedCache3SUM_Alias_a2387e9e7b890e99
import Definitions.Def_WeightedCache3SUM_Alias_a02564c7d1f1443e
import Theorems.Thm_ThreeSum_LightReportingSuffixBoxes_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_1d08961f6f3268cd
import Definitions.Def_WeightedCache3SUM_Alias_b15542bf609bcf98
import Definitions.Def_WeightedCache3SUM_Alias_362a3b2d8940306a
import Definitions.Def_WeightedCache3SUM_Alias_40e937d67ef507b4
import Definitions.Def_WeightedCache3SUM_Alias_dfc7d85d435022ae
import Definitions.Def_WeightedCache3SUM_Alias_c19df7a51d8d0351
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightScaleArray_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_9ec307913a0c2e1a
import Definitions.Def_WeightedCache3SUM_Alias_70e2e63cbf342643
import Definitions.Def_WeightedCache3SUM_Alias_805a48d522fdb6f4
import Definitions.Def_WeightedCache3SUM_Alias_8564fa03cd3297d3
import Theorems.Thm_ThreeSum_LightSign_program_meets
import Theorems.Thm_ThreeSum_LightSignedBoxSetup_program_meets
import Theorems.Thm_ThreeSum_LightSignedLeafGeneral_program_meets
import Theorems.Thm_ThreeSum_LightSignedLeafTable_program_meets
import Theorems.Thm_ThreeSum_LightSignedLeaf_program_meets
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets
import Theorems.Thm_ThreeSum_LightSourceBuild_program_meets
import Theorems.Thm_ThreeSum_LightSourceGather_program_meets
import Theorems.Thm_ThreeSum_LightSourceHistogram_program_meets
import Theorems.Thm_ThreeSum_LightSourceOccurrenceArray_program_meets
import Theorems.Thm_ThreeSum_LightSourceResidues_program_meets
import Theorems.Thm_ThreeSum_LightSparseQuery_program_meets
import Theorems.Thm_ThreeSum_LightStageLookup_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_meets
import Theorems.Thm_ThreeSum_LightSwitchDepth_program_meets
import Theorems.Thm_ThreeSum_LightSwitch_program_meets
import Theorems.Thm_ThreeSum_LightWeightDecode_program_meets
import Theorems.Thm_ThreeSum_LightWeightRow_program_meets
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightWeightedScore_program_meets
import Theorems.Thm_ThreeSum_LightZetaCell_program_meets
import Theorems.Thm_ThreeSum_LightZetaPass_program_meets
import Theorems.Thm_ThreeSum_LightZetaStages_program_meets
import Theorems.Thm_ThreeSum_ReportingHostPairSegments_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightSharedReportingBank
open Light GlobalEncoding SharedReportingBankLayout SharedReportingBankLevels
open SharedReportingBankRows
set_option maxHeartbeats 3800000
set_option maxRecDepth 16000

theorem ThreeSum.LightSharedReportingBank.program_meets_w3sum_ac885d1 {lim : Limits} {μ : ℕ → ℤ} {fB fC : ℕ → ℤ}
    {header record base NB NC g h J K occ d : ℕ} {p shift : ℤ}
    (H : SourceBandBankData.Stored μ fB fC header NB NC g h J (2*h*J) occ p shift)
    (hw : (lim.space : ℤ) ≤ lim.word) (hKpos : 0 < K)
    (hK : K ≤ LightSwitchDepth.depth J+1)
    (hocc : occ+LightBlockSourceCatalog.count h J*J ≤ header)
    (hsource : SourceBandBankData.finish header NB NC g h J (2*h*J) ≤ record)
    (hslab : record+5*K*total h J NB NC g ≤ base)
    (hspace : rowBase base h J K (total h J NB NC g) ≤ lim.space)
    (hword : (controlWord h J K NB NC g : ℤ) ≤ lim.word)
    (R : ∀ q < total h J NB NC g,
      LightSharedReportingLevels.Resources lim (rowBase base h J K q) h J K g g (d+2)) :
    Meets lim program 66 d
      [h,J,K,SourceBandBankData.first header,SourceBandBankLayout.span h J (2*h*J),
        LightBlockSourceCatalog.count h J,BandPartition.size NB g,BandPartition.size NC g,
        localChoose h,localPairs h,record,base] μ (time h J K NB NC g)
      (fun result ν => result=(rowBase base h J K (total h J NB NC g) : ℤ) ∧
        Done ν record base h J K NB NC g (total h J NB NC g) fB fC p shift ∧
        Kept μ ν record ∧ KeptBut μ ν base record (5*K*total h J NB NC g)) := by sorry
