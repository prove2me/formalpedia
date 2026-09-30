-- Prove2me | Theorems.Thm_WeakGoldbach_verified_two_odd_primes_to_4e18
-- name    : WeakGoldbach.verified_two_odd_primes_to_4e18
-- status  : Open
-- author  : @jjosh
-- created : 2026-09-11T14:24:54.587287+00:00
-- url     : https://prove2.me/theorems/32c20b3b-fcb5-4b59-a576-99fd53cf35ce
-- title:
--   Verified odd-prime binary Goldbach range $[6,\, 4\cdot 10^{18}]$
-- statement:
--   For every even natural number $m$ with
--
--   $$
--   6 \le m \le 4\cdot 10^{18},
--   $$
--
--   there exist **odd** primes $p$ and $q$ with $m = p + q$.
--
--   This is the odd-prime strengthening of the verified binary Goldbach range. A partition through the prime $2$ exists exactly when $m - 2$ is prime; the Oliveira e Silva–Herzog–Pardi partition data records that no even $m \ge 6$ in the range is forced through $2$, so an odd-prime partition always exists. This is the ingredient needed to upgrade ternary representations to all-odd representations.
-- source:
--   T. Oliveira e Silva, S. Herzog, and S. Pardi, Empirical verification of the even Goldbach conjecture and computation of prime gaps up to 4·10^18, doi:10.1090/s0025-5718-2013-02787-1

import Mathlib

namespace WeakGoldbach

theorem verified_two_odd_primes_to_4e18 (m : ℕ) (h6 : 6 ≤ m)
    (hB : m ≤ 4 * 10 ^ 18) (he : Even m) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Odd p ∧ Odd q ∧ m = p + q := by
  sorry

end WeakGoldbach
