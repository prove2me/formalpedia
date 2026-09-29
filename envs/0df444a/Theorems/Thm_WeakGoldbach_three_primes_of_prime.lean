-- Prove2me | Theorems.Thm_WeakGoldbach_three_primes_of_prime
-- name    : WeakGoldbach.three_primes_of_prime
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-22T15:57:59.98281+00:00
-- url     : https://prove2.me/theorems/3bff56b1-013c-46b3-9d28-ac731cda1181
-- title:
--   Weak Goldbach for prime $p$: singleton prime multiset
-- statement:
--   Every prime $p$ is the sum of at most three primes: the singleton multiset $\{p\}$ has cardinality $1 \le 3$, its only member $p$ is prime by hypothesis, and its sum is $p$. This generalizes the small cases $n = 3$ and $n = 5$ of the weak Goldbach mission.

import Mathlib

set_option autoImplicit false

theorem WeakGoldbach.three_primes_of_prime (p : ℕ) (hp : Nat.Prime p) :
    ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ q ∈ s, Nat.Prime q) ∧ s.sum = p := by sorry
