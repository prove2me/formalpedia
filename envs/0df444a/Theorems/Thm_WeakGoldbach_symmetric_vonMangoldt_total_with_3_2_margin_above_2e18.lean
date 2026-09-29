-- Prove2me | Theorems.Thm_WeakGoldbach_symmetric_vonMangoldt_total_with_3_2_margin_above_2e18
-- name    : WeakGoldbach.symmetric_vonMangoldt_total_with_3_2_margin_above_2e18
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T21:12:57.204294+00:00
-- url     : https://prove2.me/theorems/27d2e60f-7f82-4072-a386-2c96ef44cda6
-- title:
--   A 3/2 margin for the full symmetric von Mangoldt sum
-- statement:
--   For every natural number m greater than 2 times 10^18, the full symmetric von Mangoldt sum over offsets 0 <= t < m-1 is at least (3/2) times m times the singular-series factor over odd prime divisors of 2m. This quantitative margin is intended to absorb the central diagonal term.
-- source:
--   Auxiliary stronger full-sum estimate for the off-diagonal symmetric von Mangoldt lower bound.

import Mathlib

namespace WeakGoldbach
theorem symmetric_vonMangoldt_total_with_3_2_margin_above_2e18 (m : Nat) (hm : 2 * 10 ^ 18 < m) :
    (3 / 2 : Real) * Finset.prod ((2 * m).primeFactors.filter (fun p => 2 < p)) (fun p => ((p : Real) - 1) / ((p : Real) - 2)) * (m : Real) <=
      Finset.sum (Finset.range (m - 1)) (fun t => (ArithmeticFunction.vonMangoldt (m - t) : Real) * (ArithmeticFunction.vonMangoldt (m + t) : Real)) := by sorry
end WeakGoldbach
