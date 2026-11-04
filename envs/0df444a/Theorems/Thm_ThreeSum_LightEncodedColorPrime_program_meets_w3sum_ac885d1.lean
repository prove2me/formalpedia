-- Prove2me | Theorems.Thm_ThreeSum_LightEncodedColorPrime_program_meets_w3sum_ac885d1
-- name    : ThreeSum.LightEncodedColorPrime.program_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:55:51.940032+00:00
-- url     : https://prove2.me/theorems/d2894fc6-54c6-4ab9-a5f2-8a2f3a13c6f5
-- title:
--   Light Encoded Color Prime: program meets
-- statement:
--   The Light Encoded Color Prime construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightEncodedColorPrime.lean#L46-L134
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightEncodedColorPrime.lean#L46-L134

import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrimeCore
import Definitions.Def_Submission_ThreeSum_SourceFiniteRetention
import Definitions.Def_Submission_ThreeSum_LightBandPrimeStage
import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrime
import Theorems.Thm_ThreeSum_LightBalancedOffset_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_f4d14ad9782635c8
import Theorems.Thm_ThreeSum_LightBandCandidates_program_meets
import Theorems.Thm_ThreeSum_LightBandEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Theorems.Thm_ThreeSum_LightBandPartition_program_meets
import Theorems.Thm_ThreeSum_LightBandPreprocessing_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_4c7c7c4548f5a674
import Theorems.Thm_ThreeSum_LightBandPrimeConstruction_program_meets
import Theorems.Thm_ThreeSum_LightBandPrimeDepth_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_7e2b05f783284e0e
import Theorems.Thm_ThreeSum_LightBandPrimeSetup_program_meets
import Theorems.Thm_ThreeSum_LightBandPrimeStage_program_meets
import Theorems.Thm_ThreeSum_LightBandRawACatalog_program_meets
import Theorems.Thm_ThreeSum_LightBandRawAColor_program_meets
import Theorems.Thm_ThreeSum_LightBandRawA_program_meets
import Theorems.Thm_ThreeSum_LightBandWeightedScoreSlice_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_2ea73ff18fd48136
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
import Definitions.Def_WeightedCache3SUM_Alias_5905e9e55ae598d9
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
open ThreeSum ThreeSum.LightEncodedColorPrime
open Light BandPartition BandCandidateRows BandRawA SourceFiniteInputs
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ}

theorem ThreeSum.LightEncodedColorPrime.program_meets_w3sum_ac885d1 {av ae bv be cv ce tables rec vals g M y free maxMod U : ℕ} {hg : 0 < g}
    {originalA originalB originalC A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)} {rA : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hy : 0 < y)
    (hav : av+A.length ≤ free) (hbv : bv+B.length ≤ free) (hcv : cv+C.length ≤ free)
    (hae : ae+2 ≤ free) (hbe : be+2 ≤ free) (hce : ce+2 ≤ free)
    (hrec : rec+4*count A.length B.length C.length g ≤ free)
    (hspace : LightEncodedColorPrimeCore.space free maxMod g M y U ≤ lim.space)
    (hword : (word maxMod A.length B.length C.length g M y U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 maxMod+10 ≤ lim.depth)
    (hA : ∀ z ∈ originalA, |z| ≤ (U : ℤ))
    (hB : ∀ z ∈ originalB, |z| ≤ (U : ℤ))
    (hC : ∀ z ∈ originalC, |z| ≤ (U : ℤ))
    (H : SourceFiniteData.Normalized μ av ae bv be cv ce tables rec vals g hg
      originalA originalB originalC A B C hsA hsB hsC rA)
    (hmax : (4*y)^(LightBandPrimeDepth.depth M y+1) ≤ maxMod) :
    Meets lim program 24 d [av,ae,bv,be,cv,ce,g,rec,M,y,free] μ
      (time maxMod A.length B.length C.length g M y U)
      (fun result ν =>
        result=(moduli A B C g hg hsA hsB hsC y (LightBandPrimeDepth.depth M y) : ℤ) ∧
        EncodedColorPrimeData.Stored ν free M y (moduli A B C g hg hsA hsB hsC y) ∧ Kept μ ν free) := by sorry
