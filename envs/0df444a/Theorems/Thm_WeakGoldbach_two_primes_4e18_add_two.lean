-- Prove2me | Theorems.Thm_WeakGoldbach_two_primes_4e18_add_two
-- name    : WeakGoldbach.two_primes_4e18_add_two
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-11T02:57:57.979866+00:00
-- url     : https://prove2.me/theorems/42ccc99a-d1b1-4c5b-bbb4-d1b6172bbdd2
-- title:
--   $4\cdot 10^{18} + 2$ is a sum of two primes
-- statement:
--   There exist primes $p$ and $q$ with
--
--   $$
--   4\cdot 10^{18} + 2 = p + q.
--   $$
--
--   An explicit witness is
--
--   $$
--   4\cdot 10^{18} + 2 = 653 + 3{,}999{,}999{,}999{,}999{,}999{,}349,
--   $$
--
--   where $653$ is prime and $r = 3{,}999{,}999{,}999{,}999{,}999{,}349$ is certified prime by Pocklington's theorem via the complete factorization $r - 1 = 2^2 \cdot 3^6 \cdot 31 \cdot 61 \cdot 283 \cdot 491 \cdot 5220511$.
--
--   This single value is the boundary case of the prime-ladder reduction for the ternary Goldbach verification: the ladder rungs guarantee $n - p \le 4\cdot 10^{18} + 2$ while the verified binary range reaches only $4\cdot 10^{18}$.
-- source:
--   Boundary value needed by the prime-ladder reduction in Helfgott–Platt, arXiv:1305.3062v2 §4; explicit witness $653 + 3{,}999{,}999{,}999{,}999{,}999{,}349$

import Mathlib

namespace WeakGoldbach

theorem two_primes_4e18_add_two :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ 4 * 10 ^ 18 + 2 = p + q := by
  sorry

end WeakGoldbach
