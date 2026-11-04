-- Prove2me | Theorems.Thm_ThreeSum_LightBandPrimeMinimum_program_meets_w3sum_ac885d1
-- name    : ThreeSum.LightBandPrimeMinimum.program_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:55:43.255187+00:00
-- url     : https://prove2.me/theorems/74639e22-103d-478d-90ae-7ce475bbff5f
-- title:
--   Light Band Prime Minimum: program meets
-- statement:
--   The Light Band Prime Minimum construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPrimeMinimum.lean#L49-L172
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPrimeMinimum.lean#L49-L172

import Definitions.Def_Submission_ThreeSum_LightBandWeightedScore
import Definitions.Def_Submission_ThreeSum_BandPrimeChoice
import Definitions.Def_Submission_ThreeSum_LightBandPrimeMinimum
import Theorems.Thm_ThreeSum_LightBandEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
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
open ThreeSum ThreeSum.LightBandPrimeMinimum
open Light BandCandidateRows BandWeightedScore BandPrimeChoice
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ} {a b c nA nB nC g recs q aux s free maxMod U : ℕ}

theorem ThreeSum.LightBandPrimeMinimum.program_meets_w3sum_ac885d1 (primes : ℕ → ℕ) (rs : List Record)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + Nat.clog 2 maxMod + 7 ≤ lim.depth) (hg : 0 < g) (hq : 0 < q)
    (hs : 0 < s) (ha : a + nA ≤ free) (hb : b + nB ≤ free) (hc : c + nC ≤ free) (hrecs : recs + 4 * rs.length ≤ free)
    (haux : aux + s ≤ free) (hspace : LightWeightedScore.space free maxMod g U ≤ lim.space)
    (hword : (LightBandWeightedScore.word maxMod nA nB nC g rs.length s U : ℤ) ≤ lim.word)
    (hrecords : Seg μ recs (cells rs)) (hflag : ∀ r ∈ rs, r.flag = 0 ∨ r.flag = 1)
    (hvalid : ∀ r ∈ rs, r.flag = 1 → r.a * g ≤ nA ∧ r.b * g ≤ nB ∧ r.c * g ≤ nC) (hA : ∀ i < nA, |μ (a + i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b + i)| ≤ (U : ℤ)) (hC : ∀ i < nC, |μ (c + i)| ≤ (U : ℤ))
    (hread : ∀ i < s, μ (aux + i) = (primes i : ℤ)) (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i = primes j → i = j)
    (hproduct : ∀ i < s, ∀ j < s, q * primes i * primes j ≤ maxMod) :
    Meets lim program 17 d [a, b, c, nA, nB, nC, g, recs, rs.length, q, aux, s, free] μ (time maxMod g rs.length s U)
      (fun result ν =>
        result =
            (chosenPrime primes s q nA nB nC g (fun i => μ (a + i)) (fun i => μ (b + i)) (fun i => μ (c + i)) rs : ℤ) ∧
          Kept μ ν free) := by sorry
