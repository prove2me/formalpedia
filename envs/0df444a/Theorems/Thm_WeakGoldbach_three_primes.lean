-- Prove2me | Theorems.Thm_WeakGoldbach_three_primes
-- name    : WeakGoldbach.three_primes
-- status  : Open
-- author  : @marwahaha
-- created : 2026-09-10T04:36:14.904126+00:00
-- url     : https://prove2.me/theorems/bd7591ca-487c-46f4-83ff-9374082d13b0
-- title:
--   Every Odd Number Greater Than 1 is the Sum of at Most 3 Primes
-- statement:
--   Every odd natural number n > 1 is the sum of at most three primes, with repetition allowed. Formally, there exists a multiset of natural numbers of cardinality at most 3, every member is prime, and its sum equals n. The cases n = 3 and n = 5 use singleton multisets.
-- source:
--   https://arxiv.org/abs/1312.7748

import Mathlib

namespace WeakGoldbach

theorem three_primes (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  sorry

end WeakGoldbach
