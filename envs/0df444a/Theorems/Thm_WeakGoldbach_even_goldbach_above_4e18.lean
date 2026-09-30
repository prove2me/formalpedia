-- Prove2me | Theorems.Thm_WeakGoldbach_even_goldbach_above_4e18
-- name    : WeakGoldbach.even_goldbach_above_4e18
-- status  : Open
-- author  : @jjosh
-- created : 2026-09-11T14:42:52.22898+00:00
-- url     : https://prove2.me/theorems/910e9a05-1136-4cf7-a914-0afa4dfc1a9c
-- title:
--   Even Goldbach above the verified range $4\cdot 10^{18}$
-- statement:
--   For every even natural number $n > 4\cdot 10^{18}$ there exist primes $p, q$ with $n = p + q$.
--
--   This is the unproved tail of the even Goldbach conjecture: the claim is exactly the part of Goldbach's conjecture that lies beyond the largest computationally verified bound $4\cdot 10^{18}$ (Oliveira e Silva–Herzog–Pardi). Together with the verified range it is equivalent to the full even Goldbach conjecture.
-- source:
--   Standard formulation; the verified counterpart below $4\cdot 10^{18}$ is doi:10.1090/s0025-5718-2013-02787-1

import Mathlib

namespace WeakGoldbach

theorem even_goldbach_above_4e18 (n : ℕ) (h : 4 * 10 ^ 18 < n) (he : Even n) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q := by
  sorry

end WeakGoldbach
