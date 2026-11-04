-- Prove2me | Theorems.Thm_ThreeSum_LightPrimeChain_chosenPrime_contracts
-- name    : ThreeSum.LightPrimeChain.chosenPrime_contracts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:54:27.371944+00:00
-- url     : https://prove2.me/theorems/b9470ee7-ea22-46f0-b631-11fdc12c9139
-- title:
--   Light Prime Chain: chosen Prime contracts
-- statement:
--   The Light Prime Chain construction uses the chosen Prime contracts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimeChain.lean#L93-L107
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimeChain.lean#L93-L107

import Definitions.Def_Submission_ThreeSum_LightPrimeMinimum
import Definitions.Def_Submission_ThreeSum_PrimeChain
import Definitions.Def_Submission_ThreeSum_LightPrimeChain
set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimeChain
open Light WeightedScore LightPrimeMinimum Finset
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem ThreeSum.LightPrimeChain.chosenPrime_contracts (primes : ℕ → ℕ) (s q nA nB nC : ℕ)
    (A B C : ℕ → ℤ) (y M : ℕ) (hy : 1 < y)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i = primes j → i = j)
    (hlo : ∀ i < s, y ≤ primes i)
    (hbound : ∀ t ∈ ModuloCounts.triples nA nB nC,
      (ModuloCounts.difference A B C t).natAbs ≤ M) :
    s * score primes s (q*chosenPrime primes s q nA nB nC A B C) nA nB nC A B C ≤
      Nat.log y M * score primes s q nA nB nC A B C := by sorry
