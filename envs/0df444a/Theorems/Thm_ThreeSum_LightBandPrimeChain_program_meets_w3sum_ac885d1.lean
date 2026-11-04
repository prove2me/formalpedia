-- Prove2me | Theorems.Thm_ThreeSum_LightBandPrimeChain_program_meets_w3sum_ac885d1
-- name    : ThreeSum.LightBandPrimeChain.program_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:14:00.662079+00:00
-- url     : https://prove2.me/theorems/46310439-6cf3-4786-9bfe-62f85c3d23de
-- title:
--   Light Band Prime Chain: program meets
-- statement:
--   A closed, literal program executes the common contracting prime choices.
--   No list of choices, precomputed scores, or semantic subroutine is supplied.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPrimeChain.lean#L53-L179
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPrimeChain.lean#L53-L179

import Definitions.Def_Submission_ThreeSum_LightBandPrimeMinimum
import Definitions.Def_Submission_ThreeSum_LightBandPrimeChain
import Theorems.Thm_ThreeSum_LightBandEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
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
import Theorems.Thm_ThreeSum_LightPrimeChain_program_meets
import Theorems.Thm_ThreeSum_LightPrimeMinimum_program_meets
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightScaleArray_program_meets
import Theorems.Thm_ThreeSum_LightWeightedScore_program_meets
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPrimeChain
open Light BandCandidateRows BandPrimeChoice
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ} {a b c nA nB nC g recs aux s levels free maxMod U Y : ℕ}

theorem ThreeSum.LightBandPrimeChain.program_meets_w3sum_ac885d1 (primes : ℕ → ℕ) (rs : List Record)
    (hw : (lim.space : ℤ) ≤ lim.word) (hs : 0 < s) (hg : 0 < g) (ha : a + nA ≤ free) (hb : b + nB ≤ free)
    (hc : c + nC ≤ free) (hrecs : recs + 4 * rs.length ≤ free) (haux : aux + s ≤ free)
    (hspace : space free maxMod g U levels ≤ lim.space)
    (hword : (LightBandWeightedScore.word maxMod nA nB nC g rs.length s U : ℤ) ≤ lim.word)
    (hd : d + Nat.clog 2 maxMod + 8 ≤ lim.depth) (hrecords : Seg μ recs (cells rs))
    (hflag : ∀ r ∈ rs, r.flag = 0 ∨ r.flag = 1)
    (hvalid : ∀ r ∈ rs, r.flag = 1 → r.a * g ≤ nA ∧ r.b * g ≤ nB ∧ r.c * g ≤ nC) (hA : ∀ i < nA, |μ (a + i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b + i)| ≤ (U : ℤ)) (hC : ∀ i < nC, |μ (c + i)| ≤ (U : ℤ))
    (hread : ∀ i < s, μ (aux + i) = (primes i : ℤ)) (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i = primes j → i = j) (hhi : ∀ i < s, primes i ≤ Y)
    (hmax : Y ^ (levels + 1) ≤ maxMod) :
    Meets lim program 18 d [a, b, c, nA, nB, nC, g, recs, rs.length, aux, s, levels, free] μ
      (time maxMod g rs.length s U levels)
      (fun result ν =>
        result =
            (modulus primes s nA nB nC g (fun i => μ (a + i)) (fun i => μ (b + i)) (fun i => μ (c + i)) rs levels : ℤ) ∧
          (∀ i ≤ levels,
              ν (free + i) =
                (modulus primes s nA nB nC g (fun j => μ (a + j)) (fun j => μ (b + j)) (fun j => μ (c + j)) rs i : ℤ)) ∧
            Kept μ ν free) := by sorry
