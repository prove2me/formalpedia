-- Prove2me | Theorems.Thm_ThreeSum_BandPrimeChoice_modulus_initial_bound
-- name    : ThreeSum.BandPrimeChoice.modulus_initial_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:07:24.631172+00:00
-- url     : https://prove2.me/theorems/e0643e53-1c7e-43cd-9b26-95cddb59c2d6
-- title:
--   Band Prime Choice: modulus initial bound
-- statement:
--   The Band Prime Choice construction uses the modulus initial bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeChoice.lean#L116-L126
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeChoice.lean#L116-L126

import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Definitions.Def_Submission_ThreeSum_BandPrimeChoice
set_option autoImplicit false
open ThreeSum ThreeSum.BandPrimeChoice
open BandCandidateRows BandWeightedScore Finset
open scoped BigOperators
set_option maxHeartbeats 1400000
set_option maxRecDepth 8000

theorem ThreeSum.BandPrimeChoice.modulus_initial_bound (primes : ℕ → ℕ) (s nA nB nC g y U r : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) (hy : 1 < y)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j)
    (hlo : ∀ i < s, y ≤ primes i)
    (hA : ∀ i < nA, |A i| ≤ (U : ℤ)) (hB : ∀ i < nB, |B i| ≤ (U : ℤ))
    (hC : ∀ i < nC, |C i| ≤ (U : ℤ)) :
    s^r*score primes s (modulus primes s nA nB nC g A B C rs r) nA nB nC g A B C rs ≤
      (Nat.log y (3*U))^r*(rs.length*(s*g^3)) := by sorry
