-- Prove2me | Theorems.Thm_WeakGoldbach_verified_two_primes_4e14_to_4e18
-- name    : WeakGoldbach.verified_two_primes_4e14_to_4e18
-- status  : Open
-- author  : @jjosh
-- created : 2026-09-11T04:12:44.217059+00:00
-- url     : https://prove2.me/theorems/24c6e94b-2b96-4f10-b16d-486fa48068eb
-- title:
--   Verified binary Goldbach range $(4\cdot 10^{14},\, 4\cdot 10^{18}]$
-- statement:
--   For every even natural number $m$ with
--
--   $$
--   4\cdot 10^{14} < m \le 4\cdot 10^{18},
--   $$
--
--   there exist primes $p$ and $q$ with $m = p + q$.
--
--   This is the extension segment of the verified binary Goldbach range: Richstein's computation reaches $4\cdot 10^{14}$, and Oliveira e Silva–Herzog–Pardi extend it to $4\cdot 10^{18}$. Together with `Richstein2001.even_goldbach_up_to_4e14` it gives the full verified range through $4\cdot 10^{18}$.
-- source:
--   T. Oliveira e Silva, S. Herzog, and S. Pardi, Empirical verification of the even Goldbach conjecture and computation of prime gaps up to 4·10^18, Math. Comp. 83 (2014), no. 288, 2033–2060 (the segment above Richstein's 4·10^14)

import Mathlib

namespace WeakGoldbach

theorem verified_two_primes_4e14_to_4e18 (m : ℕ) (hlo : 4 * 10 ^ 14 < m)
    (hB : m ≤ 4 * 10 ^ 18) (he : Even m) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ m = p + q := by
  sorry

end WeakGoldbach
