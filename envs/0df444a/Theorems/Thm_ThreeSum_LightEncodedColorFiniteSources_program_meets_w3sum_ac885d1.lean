-- Prove2me | Theorems.Thm_ThreeSum_LightEncodedColorFiniteSources_program_meets_w3sum_ac885d1
-- name    : ThreeSum.LightEncodedColorFiniteSources.program_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T18:03:11.960202+00:00
-- url     : https://prove2.me/theorems/69eeccfb-98b1-4a88-9b1e-cc191f24515c
-- title:
--   Light Encoded Color Finite Sources: program meets
-- statement:
--   The Light Encoded Color Finite Sources construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightEncodedColorFiniteSources.lean#L32-L92
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightEncodedColorFiniteSources.lean#L32-L92

import Definitions.Def_Submission_ThreeSum_EncodedColorSourcesCosts
import Definitions.Def_Submission_ThreeSum_SourceFiniteRetention
import Definitions.Def_Submission_ThreeSum_LightEncodedColorFiniteSources
import Theorems.Thm_ThreeSum_BandScales_bandSize_pos
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
import Definitions.Def_WeightedCache3SUM_Alias_f4dfed36bb9fd46e
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
open ThreeSum ThreeSum.LightEncodedColorFiniteSources
open Light Scales TrimScales BandScales
variable {lim : Limits} {d : ℕ}

theorem ThreeSum.LightEncodedColorFiniteSources.program_meets_w3sum_ac885d1 {μ : ℕ → ℤ} {free av ae bv be cv ce tables rec vals n p U M : ℕ} [NeZero M]
    {originalA originalB originalC A B C xs : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)} {rA : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+256*mu n+17 ≤ lim.depth) (hn : 0 < n) (hp : 0 < p)
    (hA : originalA.length ≤ n) (hB : originalB.length ≤ n) (hC : originalC.length ≤ n)
    (hav : av+n ≤ free) (hae : ae+2+2*n ≤ free)
    (hbv : bv+n ≤ free) (hbe : be+2+2*n ≤ free)
    (hcv : cv+n ≤ free) (hce : ce+2+2*n ≤ free)
    (htables : tables+ColorBandBounds.count n (bandSize n) ≤ free)
    (hrecords : rec+4*ColorBandBounds.count n (bandSize n) ≤ free)
    (hcatalog : LightBandRawA.space vals (ColorBandBounds.count n (bandSize n)) (bandSize n) ≤ free)
    (hspace : SourceFiniteCosts.space (base free n p M xs) n p U M ≤ lim.space)
    (hword : (SourceFiniteCosts.word n p U M : ℤ) ≤ lim.word)
    (hboundB : ∀ z ∈ originalB, |z| ≤ (U : ℤ)) (hboundC : ∀ z ∈ originalC, |z| ≤ (U : ℤ))
    (H : SourceFiniteData.Normalized μ av ae bv be cv ce tables rec vals (bandSize n) (bandSize_pos n)
      originalA originalB originalC A B C hsA hsB hsC rA)
    (hcover : LightCoverKeyData.Stored μ free (microHalf (inputBits n)) (blockCount (inputBits n)))
    (hwanted : LightWantedSetup.Output μ
      (LightGuardedWanted.wantedFree free (microHalf (inputBits n)) (blockCount (inputBits n)) xs.length) M
      (LightGuardedWanted.left p xs) (LightGuardedWanted.right (microHalf (inputBits n)) (blockCount (inputBits n)))
      (3*xs.length) (LightGuardedWanted.totalKeys (microHalf (inputBits n)) (blockCount (inputBits n)))
      (RawAKeyLists.selected M p xs (microHalf (inputBits n)) (blockCount (inputBits n)))) :
    Meets lim LightEncodedColorSources.program 80 d (args free bv be cv ce n p xs.length) μ
      (EncodedColorSourcesCosts.time n p U M)
      (fun r ν =>
        SourceFiniteData.Normalized ν av ae bv be cv ce tables rec vals (bandSize n) (bandSize_pos n)
          originalA originalB originalC A B C hsA hsB hsC rA ∧
        SourceFiniteData.Stored ν (base free n p M xs) (bandSize n) p
          (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) B C
          (RawAKeyLists.selected M p xs (microHalf (inputBits n)) (blockCount (inputBits n)) : ℤ) r ∧
        LightCoverKeyData.Stored ν free (microHalf (inputBits n)) (blockCount (inputBits n)) ∧
        LightWantedSetup.Output ν
          (LightGuardedWanted.wantedFree free (microHalf (inputBits n)) (blockCount (inputBits n)) xs.length) M
          (LightGuardedWanted.left p xs) (LightGuardedWanted.right (microHalf (inputBits n)) (blockCount (inputBits n)))
          (3*xs.length) (LightGuardedWanted.totalKeys (microHalf (inputBits n)) (blockCount (inputBits n)))
          (RawAKeyLists.selected M p xs (microHalf (inputBits n)) (blockCount (inputBits n))) ∧
        Kept μ ν (base free n p M xs)) := by sorry
