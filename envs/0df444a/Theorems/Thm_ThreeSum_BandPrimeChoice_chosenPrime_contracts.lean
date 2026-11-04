-- Prove2me | Theorems.Thm_ThreeSum_BandPrimeChoice_chosenPrime_contracts
-- name    : ThreeSum.BandPrimeChoice.chosenPrime_contracts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:33:46.887937+00:00
-- url     : https://prove2.me/theorems/f35421c1-fb01-4e84-a526-61ea86591108
-- title:
--   Band Prime Choice: chosen Prime contracts
-- statement:
--   The Band Prime Choice construction uses the chosen Prime contracts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeChoice.lean#L43-L57
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeChoice.lean#L43-L57

import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Definitions.Def_Submission_ThreeSum_BandPrimeChoice
import Theorems.Thm_ThreeSum_LightPrimeChain_chosenPrime_contracts

set_option autoImplicit false
open ThreeSum ThreeSum.BandPrimeChoice
open BandCandidateRows BandWeightedScore Finset
open scoped BigOperators
set_option maxHeartbeats 1400000
set_option maxRecDepth 8000

theorem ThreeSum.BandPrimeChoice.chosenPrime_contracts (primes : ℕ → ℕ) (s q nA nB nC g y U : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) (hy : 1 < y)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j)
    (hlo : ∀ i < s, y ≤ primes i)
    (hA : ∀ i < nA, |A i| ≤ (U : ℤ)) (hB : ∀ i < nB, |B i| ≤ (U : ℤ))
    (hC : ∀ i < nC, |C i| ≤ (U : ℤ)) :
    s*score primes s (q*chosenPrime primes s q nA nB nC g A B C rs) nA nB nC g A B C rs ≤
      Nat.log y (3*U)*score primes s q nA nB nC g A B C rs := by sorry
