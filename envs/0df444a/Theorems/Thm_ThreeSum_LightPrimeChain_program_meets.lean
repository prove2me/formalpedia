-- Prove2me | Theorems.Thm_ThreeSum_LightPrimeChain_program_meets
-- name    : ThreeSum.LightPrimeChain.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:24:28.541085+00:00
-- url     : https://prove2.me/theorems/aaaa015f-e37c-49e0-a989-6efc5a472433
-- title:
--   Light Prime Chain: program meets
-- statement:
--   The Light Prime Chain construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimeChain.lean#L363-L390
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimeChain.lean#L363-L390

import Definitions.Def_Submission_ThreeSum_LightPrimeMinimum
import Definitions.Def_Submission_ThreeSum_PrimeChain
import Definitions.Def_Submission_ThreeSum_LightPrimeChain
import Theorems.Thm_ThreeSum_LightCapacity_program_meets
import Theorems.Thm_ThreeSum_LightCyclic_program_meets
import Theorems.Thm_ThreeSum_LightKaratsuba_program_meets
import Theorems.Thm_ThreeSum_LightLookupSum_program_meets
import Theorems.Thm_ThreeSum_LightModuloCounts_program_meets
import Theorems.Thm_ThreeSum_LightPrimeMinimum_program_meets
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightWeightedScore_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimeChain
open Light WeightedScore LightPrimeMinimum Finset
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightPrimeChain.program_meets
    {μ : ℕ → ℤ} {a b c nA nB nC N aux s levels free maxMod U Y : ℕ}
    (primes : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hs : 0 < s)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (haux : aux+s ≤ free)
    (hnA : nA ≤ N) (hnB : nB ≤ N) (hnC : nC ≤ N)
    (hspace : space free maxMod N U levels ≤ lim.space)
    (hword : (LightWeightedScore.word maxMod N s U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 maxMod+6 ≤ lim.depth)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ))
    (hread : ∀ i < s, μ (aux+i) = (primes i : ℤ))
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i = primes j → i = j)
    (hhi : ∀ i < s, primes i ≤ Y)
    (hmax : Y^(levels+1) ≤ maxMod) :
    Meets lim program 0 d [a,b,c,nA,nB,nC,N,aux,s,levels,free] μ
      (time maxMod nA nB nC s U levels)
      (fun r μ' =>
        r = (modulus primes s nA nB nC
          (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) levels : ℤ) ∧
        (∀ i ≤ levels, μ' (free+i) = (modulus primes s nA nB nC
          (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) i : ℤ)) ∧
        Kept μ μ' free) := by sorry
