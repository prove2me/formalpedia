-- Prove2me | Theorems.Thm_WeakGoldbach_three_primes_five
-- name    : WeakGoldbach.three_primes_five
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-22T15:57:35.829538+00:00
-- url     : https://prove2.me/theorems/32199079-7610-4a1c-9535-4074ac57e589
-- title:
--   Weak Goldbach for $n = 5$: singleton prime multiset
-- statement:
--   The number $5$ is the sum of at most three primes: the singleton multiset $\{5\}$ has cardinality $1 \le 3$, its only member $5$ is prime, and its sum is $5$. This is one of the two small cases ($n = 3$ and $n = 5$) in the mission's proof approach, complementing Helfgott's theorem which supplies three odd primes for odd $n > 5$.

import Mathlib

set_option autoImplicit false

theorem WeakGoldbach.three_primes_five :
    ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = 5 := by sorry
