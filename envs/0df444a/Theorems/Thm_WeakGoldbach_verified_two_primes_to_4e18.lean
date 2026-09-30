-- Prove2me | Theorems.Thm_WeakGoldbach_verified_two_primes_to_4e18
-- name    : WeakGoldbach.verified_two_primes_to_4e18
-- status  : Open
-- author  : @jjosh
-- created : 2026-09-11T02:57:57.400629+00:00
-- url     : https://prove2.me/theorems/0d2f6d26-e5e4-44f2-8172-1feb62301062
-- title:
--   Verified binary Goldbach range through $4\times 10^{18}$
-- statement:
--   This is the Oliveira e Silva–Herzog–Pardi distributed verification of the even (binary) Goldbach conjecture.
--
--   For every even natural number $m$ with
--
--   $$
--   4 \le m \le 4\cdot 10^{18},
--   $$
--
--   there exist primes $p$ and $q$ with
--
--   $$
--   m = p + q.
--   $$
--
--   In the proof of the ternary Goldbach conjecture, this computation is the base on which the Helfgott–Platt prime ladder rests: for an odd $n$, one chooses a ladder rung $p$ below $n$ so that $n - p$ is a positive even number inside this verified range, and concludes $n = p + q + r$.
--
--   **Formalization Note** The statement is over `Nat` with the bound $m \le 4\cdot 10^{18}$; the summand order is $m = p + q$.
-- source:
--   T. Oliveira e Silva, S. Herzog, and S. Pardi, Empirical verification of the even Goldbach conjecture and computation of prime gaps up to 4·10^18, Math. Comp. 83 (2014), no. 288, 2033–2060, DOI 10.1090/S0025-5718-2013-02787-1; used as the binary base in Helfgott–Platt, arXiv:1305.3062v2, §1 and §4

import Mathlib

namespace WeakGoldbach

theorem verified_two_primes_to_4e18 (m : ℕ) (h4 : 4 ≤ m)
    (hB : m ≤ 4 * 10 ^ 18) (he : Even m) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ m = p + q := by
  sorry

end WeakGoldbach
