-- Prove2me | Theorems.Thm_ThreeSum_LightEncodedColorSources_program_meets_w3sum_ac885d1
-- name    : ThreeSum.LightEncodedColorSources.program_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:40:31.959394+00:00
-- url     : https://prove2.me/theorems/1be4bcc0-cca2-4aad-9543-39d0e0e040b2
-- title:
--   Light Encoded Color Sources: program meets
-- statement:
--   The Light Encoded Color Sources construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightEncodedColorSources.lean#L52-L159
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightEncodedColorSources.lean#L52-L159

import Definitions.Def_Submission_ThreeSum_EncodedColorWantedData
import Definitions.Def_Submission_ThreeSum_EncodedColorCoverData
import Definitions.Def_Submission_ThreeSum_LightSourceFinitePrepared
import Definitions.Def_Submission_ThreeSum_LightEncodedColorSources
import Theorems.Thm_ThreeSum_LightBalancedOffset_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_f4d14ad9782635c8
import Theorems.Thm_ThreeSum_LightBandCandidates_program_meets
import Theorems.Thm_ThreeSum_LightBandEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Theorems.Thm_ThreeSum_LightBandPartition_program_meets
import Theorems.Thm_ThreeSum_LightBandPreprocessing_program_meets
import Theorems.Thm_ThreeSum_LightBandRawACatalog_program_meets
import Theorems.Thm_ThreeSum_LightBandRawAColor_program_meets
import Theorems.Thm_ThreeSum_LightBandRawA_program_meets
import Theorems.Thm_ThreeSum_LightBlockBoxes_program_meets
import Theorems.Thm_ThreeSum_LightBlockCoefficients_program_meets
import Theorems.Thm_ThreeSum_LightBlockQuery_program_meets
import Theorems.Thm_ThreeSum_LightBlockSourceHashes_program_meets
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Theorems.Thm_ThreeSum_LightBoxStages_program_meets
import Theorems.Thm_ThreeSum_LightBoxSum_program_meets
import Theorems.Thm_ThreeSum_LightCanonicalBoxSum_program_meets
import Theorems.Thm_ThreeSum_LightCapacity_program_meets
import Theorems.Thm_ThreeSum_LightClassFilter_program_meets
import Theorems.Thm_ThreeSum_LightColorArray_program_meets
import Theorems.Thm_ThreeSum_LightColorBands_program_meets
import Theorems.Thm_ThreeSum_LightColorClasses_program_meets
import Theorems.Thm_ThreeSum_LightColorIndex_program_meets
import Theorems.Thm_ThreeSum_LightCoverGreedy_program_meets
import Theorems.Thm_ThreeSum_LightCoverKeyData_program_meets
import Theorems.Thm_ThreeSum_LightCoverScores_program_meets
import Theorems.Thm_ThreeSum_LightCoverSelect_program_meets
import Theorems.Thm_ThreeSum_LightCoverUpdate_program_meets
import Theorems.Thm_ThreeSum_LightCyclic_program_meets
import Theorems.Thm_ThreeSum_LightDownsetAddress_program_meets
import Theorems.Thm_ThreeSum_LightDownsetEnumerationSetup_program_meets
import Theorems.Thm_ThreeSum_LightDownsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightDownsetSize_program_meets
import Theorems.Thm_ThreeSum_LightExplicitSum_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_645c59421f5229aa
import Theorems.Thm_ThreeSum_LightHeaderBands_program_meets
import Theorems.Thm_ThreeSum_LightKaratsuba_program_meets
import Theorems.Thm_ThreeSum_LightLeafSum_program_meets
import Theorems.Thm_ThreeSum_LightLocalCounts_program_meets
import Theorems.Thm_ThreeSum_LightLocalCoverSchedule_program_meets
import Theorems.Thm_ThreeSum_LightLocalParameters_program_meets
import Theorems.Thm_ThreeSum_LightLookupSum_program_meets
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightMaskHashes_program_meets
import Theorems.Thm_ThreeSum_LightMaskMinimum_program_meets
import Theorems.Thm_ThreeSum_LightMaskUnion_program_meets
import Theorems.Thm_ThreeSum_LightModuloCounts_program_meets
import Theorems.Thm_ThreeSum_LightNatPower_program_meets
import Theorems.Thm_ThreeSum_LightNormalize_program_meets
import Theorems.Thm_ThreeSum_LightOneHot_program_meets
import Theorems.Thm_ThreeSum_LightOriginalOffset_program_meets
import Theorems.Thm_ThreeSum_LightOutputDecodeDigits_program_meets
import Theorems.Thm_ThreeSum_LightOutputDecodeDivide_program_meets
import Theorems.Thm_ThreeSum_LightPairFlags_program_meets
import Theorems.Thm_ThreeSum_LightPrimality_program_meets
import Theorems.Thm_ThreeSum_LightPrimeChain_program_meets
import Theorems.Thm_ThreeSum_LightPrimeMinimum_program_meets
import Theorems.Thm_ThreeSum_LightPrimePool_program_meets
import Theorems.Thm_ThreeSum_LightQueryBox_program_meets
import Theorems.Thm_ThreeSum_LightQueryEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightQueryWeights_program_meets
import Theorems.Thm_ThreeSum_LightRadixDigit_program_meets
import Theorems.Thm_ThreeSum_LightRadixKeys_program_meets
import Theorems.Thm_ThreeSum_LightRadixRows_program_meets
import Theorems.Thm_ThreeSum_LightRawAKeys_program_meets
import Theorems.Thm_ThreeSum_LightReportingAffine_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_c19df7a51d8d0351
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightScaleArray_program_meets
import Theorems.Thm_ThreeSum_LightSelectedPrime_program_meets
import Theorems.Thm_ThreeSum_LightSign_program_meets
import Theorems.Thm_ThreeSum_LightSignedBoxSetup_program_meets
import Theorems.Thm_ThreeSum_LightSignedLeafGeneral_program_meets
import Theorems.Thm_ThreeSum_LightSignedLeafTable_program_meets
import Theorems.Thm_ThreeSum_LightSignedLeaf_program_meets
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets
import Theorems.Thm_ThreeSum_LightSortedBands_program_meets
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
import Theorems.Thm_ThreeSum_LightWantedJoin_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_631140e497667d8d
import Theorems.Thm_ThreeSum_LightWeightDecode_program_meets
import Theorems.Thm_ThreeSum_LightWeightRow_program_meets
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightWeightedScore_program_meets
import Theorems.Thm_ThreeSum_LightZetaCell_program_meets
import Theorems.Thm_ThreeSum_LightZetaPass_program_meets
import Theorems.Thm_ThreeSum_LightZetaStages_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightEncodedColorSources
open Light GlobalEncoding LocalCoverBounds BlockSourceEncoding SourceFiniteInputs
set_option maxHeartbeats 2600000
set_option maxRecDepth 14000
variable {lim : Limits} {d : ℕ}

theorem ThreeSum.LightEncodedColorSources.program_meets_w3sum_ac885d1 {μ : ℕ → ℤ} {free bv be cv ce g p M h J cut U : ℕ} [NeZero M]
    {hg : 0 < g} {originalB originalC B C xs : List ℤ}
    {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(512*h)+17 ≤ lim.depth)
    (hp : 0 < p) (hcut : cut ≤ J*(512*h))
    (hbv : bv+originalB.length ≤ free) (hcv : cv+originalC.length ≤ free)
    (hbe : be+2 ≤ free) (hce : ce+2 ≤ free)
    (hspace : LightSourceControlsHost.space (sourceBase free p M h J xs)
      B.length C.length g p h J cut U M ≤ lim.space)
    (hword : (LightSourceControlsHost.word B.length C.length g p h J cut U M : ℤ) ≤ lim.word)
    (hB : LightBandPreprocessing.Represents μ bv be g hg originalB B hsB)
    (hC : LightBandPreprocessing.Represents μ cv ce g hg originalC C hsC)
    (hboundB : ∀ z ∈ originalB, |z| ≤ (U : ℤ)) (hboundC : ∀ z ∈ originalC, |z| ≤ (U : ℤ))
    (hcover : LightCoverKeyData.Stored μ free h J)
    (hwanted : LightWantedSetup.Output μ (LightGuardedWanted.wantedFree free h J xs.length) M
      (LightGuardedWanted.left p xs) (LightGuardedWanted.right h J)
      (3*xs.length) (LightGuardedWanted.totalKeys h J) (RawAKeyLists.selected M p xs h J)) :
    Meets lim program 80 d [h,J,cut,bv,be,cv,ce,g,p,LightGuardedWanted.wantedFree free h J xs.length,free] μ
      (time B.length C.length g p h J cut U M)
      (fun r ν =>
        SourceFiniteData.Stored ν (sourceBase free p M h J xs) g p h J cut B C
          (RawAKeyLists.selected M p xs h J : ℤ) r ∧
        LightCoverKeyData.Stored ν free h J ∧
        LightWantedSetup.Output ν (LightGuardedWanted.wantedFree free h J xs.length) M
          (LightGuardedWanted.left p xs) (LightGuardedWanted.right h J)
          (3*xs.length) (LightGuardedWanted.totalKeys h J) (RawAKeyLists.selected M p xs h J) ∧
        Kept μ ν (sourceBase free p M h J xs)) := by sorry
