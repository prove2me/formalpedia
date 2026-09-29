-- Prove2me | Theorems.Thm_WeakGoldbach_three_primes_three
-- name    : WeakGoldbach.three_primes_three
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-22T15:57:33.601227+00:00
-- url     : https://prove2.me/theorems/e83bff43-ddae-444d-9cc2-c75310919a18
-- title:
--   Weak Goldbach for $n = 3$: singleton prime multiset
-- statement:
--   The number $3$ is the sum of at most three primes: the singleton multiset $\{3\}$ has cardinality $1 \le 3$, its only member $3$ is prime, and its sum is $3$. This is one of the two small cases ($n = 3$ and $n = 5$) in the mission's proof approach, complementing Helfgott's theorem which supplies three odd primes for odd $n > 5$.

import Mathlib

set_option autoImplicit false

theorem WeakGoldbach.three_primes_three :
    ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = 3 := by sorry
