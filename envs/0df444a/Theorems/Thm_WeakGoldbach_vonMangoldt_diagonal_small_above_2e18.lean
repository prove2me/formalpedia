-- Prove2me | Theorems.Thm_WeakGoldbach_vonMangoldt_diagonal_small_above_2e18
-- name    : WeakGoldbach.vonMangoldt_diagonal_small_above_2e18
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-25T21:12:55.198991+00:00
-- url     : https://prove2.me/theorems/253481b3-2dbc-4df2-8845-9791586135a4
-- title:
--   The von Mangoldt diagonal is small above 2e18
-- statement:
--   For every natural number m greater than 2 times 10^18, the square of the von Mangoldt value at m is at most one quarter of m times the singular-series factor over odd prime divisors of 2m. This bounds the diagonal contribution when passing from the full symmetric sum to its off-diagonal part.
-- source:
--   Elementary diagonal error estimate for the symmetric von Mangoldt sum.

import Mathlib

namespace WeakGoldbach
theorem vonMangoldt_diagonal_small_above_2e18 (m : Nat) (hm : 2 * 10 ^ 18 < m) :
    ((ArithmeticFunction.vonMangoldt m : Real) ^ 2) <=
      (1 / 4 : Real) * Finset.prod ((2 * m).primeFactors.filter (fun p => 2 < p)) (fun p => ((p : Real) - 1) / ((p : Real) - 2)) * (m : Real) := by sorry
end WeakGoldbach
