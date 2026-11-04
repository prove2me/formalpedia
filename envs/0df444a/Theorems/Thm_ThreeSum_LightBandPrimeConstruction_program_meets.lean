-- Prove2me | Theorems.Thm_ThreeSum_LightBandPrimeConstruction_program_meets
-- name    : ThreeSum.LightBandPrimeConstruction.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:43:24.474+00:00
-- url     : https://prove2.me/theorems/b4f3b318-0c1e-4879-a5bc-df5ed4b8007b
-- title:
--   Light Band Prime Construction: program meets
-- statement:
--   The Light Band Prime Construction construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPrimeConstruction.lean#L74-L154
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPrimeConstruction.lean#L74-L154

import Definitions.Def_Submission_ThreeSum_LightBandPrimeChain
import Definitions.Def_Submission_ThreeSum_LightPrimePool
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_ThreeSum_LightBandPrimeConstruction
import Theorems.Thm_ThreeSum_LightBandEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_4c7c7c4548f5a674
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
open ThreeSum ThreeSum.LightBandPrimeConstruction
open Light BandCandidateRows
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ} {a b c nA nB nC g recs y levels free maxMod U : ℕ}

theorem ThreeSum.LightBandPrimeConstruction.program_meets (rs : List Record) (hw : (lim.space : ℤ) ≤ lim.word)
    (hy : 0 < y) (hg : 0 < g) (ha : a + nA ≤ free) (hb : b + nB ≤ free) (hc : c + nC ≤ free)
    (hrecs : recs + 4 * rs.length ≤ free) (hspace : space free maxMod g y U levels ≤ lim.space)
    (hword : (word maxMod nA nB nC g rs.length y U : ℤ) ≤ lim.word) (hd : d + Nat.clog 2 maxMod + 9 ≤ lim.depth)
    (hrecords : Seg μ recs (cells rs)) (hflag : ∀ r ∈ rs, r.flag = 0 ∨ r.flag = 1)
    (hvalid : ∀ r ∈ rs, r.flag = 1 → r.a * g ≤ nA ∧ r.b * g ≤ nB ∧ r.c * g ≤ nC) (hA : ∀ i < nA, |μ (a + i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b + i)| ≤ (U : ℤ)) (hC : ∀ i < nC, |μ (c + i)| ≤ (U : ℤ))
    (hmax : (4 * y) ^ (levels + 1) ≤ maxMod) :
    Meets lim program 22 d [a, b, c, nA, nB, nC, g, recs, rs.length, y, levels, free] μ
      (time maxMod g rs.length y U levels)
      (fun result ν =>
        result = (modulus y nA nB nC g (fun j => μ (a + j)) (fun j => μ (b + j)) (fun j => μ (c + j)) rs levels : ℤ) ∧
          SegN ν free (LightPrimePool.values y) ∧
            (∀ i ≤ levels,
                ν (free + 3 * y + i) =
                  (modulus y nA nB nC g (fun j => μ (a + j)) (fun j => μ (b + j)) (fun j => μ (c + j)) rs i : ℤ)) ∧
              Kept μ ν free) := by sorry
