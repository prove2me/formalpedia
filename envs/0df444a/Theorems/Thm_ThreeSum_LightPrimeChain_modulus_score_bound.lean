-- Prove2me | Theorems.Thm_ThreeSum_LightPrimeChain_modulus_score_bound
-- name    : ThreeSum.LightPrimeChain.modulus_score_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:47:36.057853+00:00
-- url     : https://prove2.me/theorems/63450ec4-fdf4-4649-b468-f6e1eb8c83c3
-- title:
--   Light Prime Chain: modulus score bound
-- statement:
--   Exact contraction for the same minimum choices returned by the program.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimeChain.lean#L110-L135
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimeChain.lean#L110-L135

import Definitions.Def_Submission_ThreeSum_LightPrimeMinimum
import Definitions.Def_Submission_ThreeSum_PrimeChain
import Definitions.Def_Submission_ThreeSum_LightPrimeChain
import Theorems.Thm_ThreeSum_PrimeChain_modulus_score_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimeChain
open Light WeightedScore LightPrimeMinimum Finset
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem ThreeSum.LightPrimeChain.modulus_score_bound (primes : ℕ → ℕ) (s nA nB nC : ℕ)
    (A B C : ℕ → ℤ) (y M r : ℕ) (hy : 1 < y)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i = primes j → i = j)
    (hlo : ∀ i < s, y ≤ primes i)
    (hbound : ∀ t ∈ ModuloCounts.triples nA nB nC,
      (ModuloCounts.difference A B C t).natAbs ≤ M) :
    s^r * score primes s (modulus primes s nA nB nC A B C r) nA nB nC A B C ≤
      (Nat.log y M)^r * score primes s 1 nA nB nC A B C := by sorry
