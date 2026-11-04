-- Prove2me | Theorems.Thm_ThreeSum_LightPrimeMinimum_program_meets
-- name    : ThreeSum.LightPrimeMinimum.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:14:42.559767+00:00
-- url     : https://prove2.me/theorems/62fa2373-89ef-461c-bc65-9c88fa8081b7
-- title:
--   Light Prime Minimum: program meets
-- statement:
--   The Light Prime Minimum construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimeMinimum.lean#L277-L300
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimeMinimum.lean#L277-L300

import Definitions.Def_Submission_ThreeSum_LightWeightedScore
import Definitions.Def_Submission_ThreeSum_LightMinimum
import Definitions.Def_Submission_ThreeSum_LightPrimeMinimum
import Theorems.Thm_ThreeSum_LightCapacity_program_meets
import Theorems.Thm_ThreeSum_LightCyclic_program_meets
import Theorems.Thm_ThreeSum_LightKaratsuba_program_meets
import Theorems.Thm_ThreeSum_LightLookupSum_program_meets
import Theorems.Thm_ThreeSum_LightModuloCounts_program_meets
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightWeightedScore_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimeMinimum
open Light WeightedScore
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightPrimeMinimum.program_meets
    {μ : ℕ → ℤ} {a b c nA nB nC q N aux s free maxMod U : ℕ}
    (primes : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hq : 0 < q) (hs : 0 < s)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (haux : aux+s ≤ free)
    (hnA : nA ≤ N) (hnB : nB ≤ N) (hnC : nC ≤ N)
    (hspace : LightWeightedScore.space free maxMod N U ≤ lim.space)
    (hword : (LightWeightedScore.word maxMod N s U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 maxMod+5 ≤ lim.depth)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ))
    (hread : ∀ i < s, μ (aux+i) = (primes i : ℤ))
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i = primes j → i = j)
    (hproduct : ∀ i < s, ∀ j < s, q*primes i*primes j ≤ maxMod) :
    Meets lim program 0 d [a,b,c,nA,nB,nC,q,N,aux,s,free] μ
      (time maxMod nA nB nC s U)
      (fun r μ' => r = (chosenPrime primes s q nA nB nC
        (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) : ℤ) ∧
          Kept μ μ' free) := by sorry
