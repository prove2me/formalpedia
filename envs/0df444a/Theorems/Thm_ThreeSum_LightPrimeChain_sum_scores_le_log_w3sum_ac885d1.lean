-- Prove2me | Theorems.Thm_ThreeSum_LightPrimeChain_sum_scores_le_log_w3sum_ac885d1
-- name    : ThreeSum.LightPrimeChain.sum_scores_le_log_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:21:23.859663+00:00
-- url     : https://prove2.me/theorems/4779c39e-4b53-4bf3-9e88-0c777e8bc005
-- title:
--   Light Prime Chain: sum scores le log
-- statement:
--   Convert the finite-prime averaging theorem to the actual array order.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimeChain.lean#L62-L91
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimeChain.lean#L62-L91

import Definitions.Def_Submission_ThreeSum_LightPrimeMinimum
import Definitions.Def_Submission_ThreeSum_PrimeChain
import Definitions.Def_Submission_ThreeSum_LightPrimeChain
import Theorems.Thm_ThreeSum_PrimeChain_sum_scores_le_log

set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimeChain
open Light WeightedScore LightPrimeMinimum Finset
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem ThreeSum.LightPrimeChain.sum_scores_le_log_w3sum_ac885d1 (primes : ℕ → ℕ) (s q nA nB nC : ℕ)
    (A B C : ℕ → ℤ) (y M : ℕ) (hy : 1 < y)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i = primes j → i = j)
    (hlo : ∀ i < s, y ≤ primes i)
    (hbound : ∀ t ∈ ModuloCounts.triples nA nB nC,
      (ModuloCounts.difference A B C t).natAbs ≤ M) :
    (∑ i ∈ range s, score primes s (q*primes i) nA nB nC A B C) ≤
      Nat.log y M * score primes s q nA nB nC A B C := by sorry
