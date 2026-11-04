-- Prove2me | Theorems.Thm_ThreeSum_BandPrimeChoice_modulus_score_bound_w3sum_ac885d1
-- name    : ThreeSum.BandPrimeChoice.modulus_score_bound_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:36:05.573357+00:00
-- url     : https://prove2.me/theorems/a8c8a45b-1634-4813-8432-388cf2207912
-- title:
--   Band Prime Choice: modulus score bound
-- statement:
--   The Band Prime Choice construction uses the modulus score bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeChoice.lean#L91-L114
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeChoice.lean#L91-L114

import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Definitions.Def_Submission_ThreeSum_BandPrimeChoice
import Theorems.Thm_ThreeSum_LightPrimeChain_modulus_score_bound
import Theorems.Thm_ThreeSum_PrimeChain_modulus_score_bound

set_option autoImplicit false
open ThreeSum ThreeSum.BandPrimeChoice
open BandCandidateRows BandWeightedScore Finset
open scoped BigOperators
set_option maxHeartbeats 1400000
set_option maxRecDepth 8000

theorem ThreeSum.BandPrimeChoice.modulus_score_bound_w3sum_ac885d1 (primes : ℕ → ℕ) (s nA nB nC g y U r : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) (hy : 1 < y)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j)
    (hlo : ∀ i < s, y ≤ primes i)
    (hA : ∀ i < nA, |A i| ≤ (U : ℤ)) (hB : ∀ i < nB, |B i| ≤ (U : ℤ))
    (hC : ∀ i < nC, |C i| ≤ (U : ℤ)) :
    s^r*score primes s (modulus primes s nA nB nC g A B C rs r) nA nB nC g A B C rs ≤
      (Nat.log y (3*U))^r*score primes s 1 nA nB nC g A B C rs := by sorry
