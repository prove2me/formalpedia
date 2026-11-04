-- Prove2me | Theorems.Thm_ThreeSum_LightEncodedColorPrimeCore_program_meets_w3sum_ac885d1
-- name    : ThreeSum.LightEncodedColorPrimeCore.program_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:04:01.560746+00:00
-- url     : https://prove2.me/theorems/8d5a0ed6-8d83-4b36-a6a1-a7c51d794201
-- title:
--   Light Encoded Color Prime Core: program meets
-- statement:
--   The Light Encoded Color Prime Core construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightEncodedColorPrimeCore.lean#L55-L171
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightEncodedColorPrimeCore.lean#L55-L171

import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeData
import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrimeCore
import Theorems.Thm_ThreeSum_LightBandEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_4c7c7c4548f5a674
import Theorems.Thm_ThreeSum_LightBandPrimeConstruction_program_meets
import Theorems.Thm_ThreeSum_LightBandPrimeDepth_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_7e2b05f783284e0e
import Theorems.Thm_ThreeSum_LightBandWeightedScoreSlice_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_2ea73ff18fd48136
import Theorems.Thm_ThreeSum_LightBlockCoefficients_program_meets
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Theorems.Thm_ThreeSum_LightCapacity_program_meets
import Theorems.Thm_ThreeSum_LightCyclic_program_meets
import Theorems.Thm_ThreeSum_LightKaratsuba_program_meets
import Theorems.Thm_ThreeSum_LightLookupSum_program_meets
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightMaskHashes_program_meets
import Theorems.Thm_ThreeSum_LightModuloCounts_program_meets
import Theorems.Thm_ThreeSum_LightOneHot_program_meets
import Theorems.Thm_ThreeSum_LightPrimality_program_meets
import Theorems.Thm_ThreeSum_LightPrimeChain_program_meets
import Theorems.Thm_ThreeSum_LightPrimeMinimum_program_meets
import Theorems.Thm_ThreeSum_LightPrimePool_program_meets
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightScaleArray_program_meets
import Theorems.Thm_ThreeSum_LightWeightedScore_program_meets
set_option autoImplicit false
open ThreeSum ThreeSum.LightEncodedColorPrimeCore
open Light BandCandidateRows EncodedColorPrimeData
set_option maxHeartbeats 2600000
set_option maxRecDepth 13000
variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ} {a b c nA nB nC g recs M y free maxMod U : ℕ}

theorem ThreeSum.LightEncodedColorPrimeCore.program_meets_w3sum_ac885d1 (rs : List Record)
    (hw : (lim.space : ℤ) ≤ lim.word) (hy : 0 < y) (hg : 0 < g) (ha : a + nA ≤ free) (hb : b + nB ≤ free)
    (hc : c + nC ≤ free) (hrecs : recs + 4 * rs.length ≤ free) (hspace : space free maxMod g M y U ≤ lim.space)
    (hword : (word maxMod nA nB nC g rs.length M y U : ℤ) ≤ lim.word) (hd : d + Nat.clog 2 maxMod + 9 ≤ lim.depth)
    (hrecords : Seg μ recs (cells rs)) (hflag : ∀ r ∈ rs, r.flag = 0 ∨ r.flag = 1)
    (hvalid : ∀ r ∈ rs, r.flag = 1 → r.a * g ≤ nA ∧ r.b * g ≤ nB ∧ r.c * g ≤ nC) (hA : ∀ i < nA, |μ (a + i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b + i)| ≤ (U : ℤ)) (hC : ∀ i < nC, |μ (c + i)| ≤ (U : ℤ))
    (hmax : (4 * y) ^ (LightBandPrimeDepth.depth M y + 1) ≤ maxMod) :
    Meets lim program 23 d [a, b, c, nA, nB, nC, g, recs, rs.length, M, y, free] μ (time maxMod g rs.length M y U)
      (fun result ν =>
        result =
            (LightBandPrimeConstruction.modulus y nA nB nC g (fun j => μ (a + j)) (fun j => μ (b + j))
                (fun j => μ (c + j)) rs (LightBandPrimeDepth.depth M y) :
              ℤ) ∧
          EncodedColorPrimeData.Stored ν free M y
              (LightBandPrimeConstruction.modulus y nA nB nC g (fun j => μ (a + j)) (fun j => μ (b + j))
                (fun j => μ (c + j)) rs) ∧
            Kept μ ν free) := by sorry
