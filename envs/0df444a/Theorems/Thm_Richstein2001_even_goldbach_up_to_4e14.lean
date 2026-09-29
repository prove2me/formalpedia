-- Prove2me | Theorems.Thm_Richstein2001_even_goldbach_up_to_4e14
-- name    : Richstein2001.even_goldbach_up_to_4e14
-- status  : Open
-- author  : @marwahaha
-- created : 2026-09-09T10:07:29.006625+00:00
-- url     : https://prove2.me/theorems/a93cdda5-d19c-4cdb-9d78-81ce8955c538
-- title:
--   Richstein finite verification of even Goldbach up to $4\cdot10^{14}$
-- statement:
--   Richstein's distributed computation verifies the even Goldbach conjecture throughout the exact finite range used in Tao's five-primes proof: every even natural number $n$ with $4\le n\le 4\cdot 10^{14}$ is a sum of two primes. This is a finite computational source theorem and does not assert the still-open conjecture beyond the verified range.
-- source:
--   Jorg Richstein, Verifying the Goldbach conjecture up to 4*10^14, Mathematics of Computation 70 (2001), 1745-1749, DOI 10.1090/S0025-5718-00-01290-4; also Tao arXiv:1201.6656v4, Theorem 1.6: https://doi.org/10.1090/S0025-5718-00-01290-4

import Mathlib

namespace Richstein2001

theorem even_goldbach_up_to_4e14 (n : ℕ)
    (h4 : 4 ≤ n) (hN : n ≤ 4 * 10 ^ 14) (he : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by sorry

end Richstein2001
