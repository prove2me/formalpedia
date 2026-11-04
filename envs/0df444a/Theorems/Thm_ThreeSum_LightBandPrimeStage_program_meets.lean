-- Prove2me | Theorems.Thm_ThreeSum_LightBandPrimeStage_program_meets
-- name    : ThreeSum.LightBandPrimeStage.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:35:46.381435+00:00
-- url     : https://prove2.me/theorems/95e65d99-805a-453b-a4a1-2a3b1f9cf2f7
-- title:
--   Light Band Prime Stage: program meets
-- statement:
--   The Light Band Prime Stage construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPrimeStage.lean#L60-L120
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPrimeStage.lean#L60-L120

import Definitions.Def_Submission_ThreeSum_BandPrimeCostBounds
import Definitions.Def_Submission_ThreeSum_BandRawAFinite
import Definitions.Def_Submission_ThreeSum_SourceBandCosts
import Definitions.Def_Submission_ThreeSum_LightBandPrimeStage
import Theorems.Thm_ThreeSum_LightBalancedOffset_program_meets
import Theorems.Thm_ThreeSum_LightBandEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_4c7c7c4548f5a674
import Theorems.Thm_ThreeSum_LightBandPrimeConstruction_program_meets
import Theorems.Thm_ThreeSum_LightBandPrimeDepth_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_7e2b05f783284e0e
import Theorems.Thm_ThreeSum_LightBandPrimeSetup_program_meets
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
import Theorems.Thm_ThreeSum_LightPrimality_program_meets
import Theorems.Thm_ThreeSum_LightPrimeChain_program_meets
import Theorems.Thm_ThreeSum_LightPrimeMinimum_program_meets
import Theorems.Thm_ThreeSum_LightPrimePool_program_meets
import Theorems.Thm_ThreeSum_LightQueryBox_program_meets
import Theorems.Thm_ThreeSum_LightQueryEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightQueryWeights_program_meets
import Theorems.Thm_ThreeSum_LightRadixDigit_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_c19df7a51d8d0351
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightScaleArray_program_meets
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
import Theorems.Thm_ThreeSum_LightWeightDecode_program_meets
import Theorems.Thm_ThreeSum_LightWeightRow_program_meets
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightWeightedScore_program_meets
import Theorems.Thm_ThreeSum_LightZetaCell_program_meets
import Theorems.Thm_ThreeSum_LightZetaPass_program_meets
import Theorems.Thm_ThreeSum_LightZetaStages_program_meets
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPrimeStage
open Light BandEnumeration BandCandidateRows Scales BandScales CostLedger
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ} {a b c n nA nB nC k recs free : ℕ}

theorem ThreeSum.LightBandPrimeStage.program_meets (A B C : Family) (hA : A.size = BandPartition.size nA (bandSize n))
    (hB : B.size = BandPartition.size nB (bandSize n)) (hC : C.size = BandPartition.size nC (bandSize n)) (hn : 0 < n)
    (hnA : nA ≤ n) (hnB : nB ≤ n) (hnC : nC ≤ n) (hR : 4 ≤ radix n)
    (hbudget : divisorBudget k n * primeWindow n ≤ candidateCount n * (4 * (k + 2) * (inputBits n + 1)))
    (hw : (lim.space : ℤ) ≤ lim.word) (ha : a + nA ≤ free) (hb : b + nB ≤ free) (hc : c + nC ≤ free)
    (hrecs : recs + 4 * (records A B C).length ≤ free)
    (hspace :
      LightBandPrimeSetup.space free (ArithmeticStageBounds.maxMod n) (bandSize n) (radix n) (primeWindow n) (n ^ k) ≤
        lim.space)
    (hword :
      (LightBandPrimeSetup.word (ArithmeticStageBounds.maxMod n) nA nB nC (bandSize n) (records A B C).length (radix n)
            (primeWindow n) (n ^ k) :
          ℤ) ≤
        lim.word)
    (hd : d + Nat.clog 2 (ArithmeticStageBounds.maxMod n) + 10 ≤ lim.depth)
    (hrecords : Seg μ recs (cells (records A B C))) (hvaluesA : ∀ i < nA, |μ (a + i)| ≤ (n ^ k : ℤ))
    (hvaluesB : ∀ i < nB, |μ (b + i)| ≤ (n ^ k : ℤ)) (hvaluesC : ∀ i < nC, |μ (c + i)| ≤ (n ^ k : ℤ)) :
    Meets lim program 24 d [a, b, c, nA, nB, nC, bandSize n, recs, (records A B C).length, radix n, primeWindow n, free]
      μ (BandPrimeCosts.timeBudget k n)
      (fun result ν =>
        result =
            (BandPrimeScales.modulus n nA nB nC (fun i => μ (a + i)) (fun i => μ (b + i)) (fun i => μ (c + i))
                (records A B C) :
              ℤ) ∧
          0 < result ∧
            4 * result ≤ (radix n : ℤ) ∧
              SegN ν free (LightPrimePool.values (primeWindow n)) ∧
                (∀ i ≤ primeDepth radix n,
                    ν (free + 3 * primeWindow n + i) =
                      (LightBandPrimeConstruction.modulus (primeWindow n) nA nB nC (bandSize n) (fun j => μ (a + j))
                          (fun j => μ (b + j)) (fun j => μ (c + j)) (records A B C) i :
                        ℤ)) ∧
                  (finiteMass n result.toNat nA nB nC (fun i => μ (a + i)) (fun i => μ (b + i)) (fun i => μ (c + i))
                          (records A B C) :
                        ℝ) ≤
                      MassScales.falseMajorant k n ∧
                    Kept μ ν free) := by sorry
