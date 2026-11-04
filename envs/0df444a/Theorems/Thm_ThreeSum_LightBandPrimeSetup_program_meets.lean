-- Prove2me | Theorems.Thm_ThreeSum_LightBandPrimeSetup_program_meets
-- name    : ThreeSum.LightBandPrimeSetup.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:03:13.435289+00:00
-- url     : https://prove2.me/theorems/8eb2e878-db9b-4f9b-8fa4-90d8b11a43dc
-- title:
--   Light Band Prime Setup: program meets
-- statement:
--   The Light Band Prime Setup construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPrimeSetup.lean#L41-L82
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPrimeSetup.lean#L41-L82

import Definitions.Def_Submission_ThreeSum_LightBandPrimeDepth
import Definitions.Def_Submission_ThreeSum_LightBandPrimeConstruction
import Definitions.Def_Submission_ThreeSum_LightBandPrimeSetup
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
open ThreeSum ThreeSum.LightBandPrimeSetup
open Light BandCandidateRows
set_option maxHeartbeats 1600000
set_option maxRecDepth 9000
variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ} {a b c nA nB nC g recs M y free maxMod U : ℕ}

theorem ThreeSum.LightBandPrimeSetup.program_meets (rs : List Record) (hw : (lim.space : ℤ) ≤ lim.word) (hy : 0 < y)
    (hg : 0 < g) (ha : a + nA ≤ free) (hb : b + nB ≤ free) (hc : c + nC ≤ free) (hrecs : recs + 4 * rs.length ≤ free)
    (hspace : space free maxMod g M y U ≤ lim.space) (hword : (word maxMod nA nB nC g rs.length M y U : ℤ) ≤ lim.word)
    (hd : d + Nat.clog 2 maxMod + 10 ≤ lim.depth) (hrecords : Seg μ recs (cells rs))
    (hflag : ∀ r ∈ rs, r.flag = 0 ∨ r.flag = 1)
    (hvalid : ∀ r ∈ rs, r.flag = 1 → r.a * g ≤ nA ∧ r.b * g ≤ nB ∧ r.c * g ≤ nC) (hA : ∀ i < nA, |μ (a + i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b + i)| ≤ (U : ℤ)) (hC : ∀ i < nC, |μ (c + i)| ≤ (U : ℤ))
    (hmax : (4 * y) ^ (LightBandPrimeDepth.depth M y + 1) ≤ maxMod) :
    Meets lim program 24 d [a, b, c, nA, nB, nC, g, recs, rs.length, M, y, free] μ (time maxMod g rs.length M y U)
      (fun result ν =>
        result =
            (LightBandPrimeConstruction.modulus y nA nB nC g (fun j => μ (a + j)) (fun j => μ (b + j))
                (fun j => μ (c + j)) rs (LightBandPrimeDepth.depth M y) :
              ℤ) ∧
          SegN ν free (LightPrimePool.values y) ∧
            (∀ i ≤ LightBandPrimeDepth.depth M y,
                ν (free + 3 * y + i) =
                  (LightBandPrimeConstruction.modulus y nA nB nC g (fun j => μ (a + j)) (fun j => μ (b + j))
                      (fun j => μ (c + j)) rs i :
                    ℤ)) ∧
              Kept μ ν free) := by sorry
