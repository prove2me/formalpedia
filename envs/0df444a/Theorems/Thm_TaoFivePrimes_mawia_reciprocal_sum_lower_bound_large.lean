-- Prove2me | Theorems.Thm_TaoFivePrimes_mawia_reciprocal_sum_lower_bound_large
-- name    : TaoFivePrimes.mawia_reciprocal_sum_lower_bound_large
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T13:55:58.556001+00:00
-- url     : https://prove2.me/theorems/bbd532c3-eebe-46c4-b84e-856e6c787d66
-- title:
--   Mawia reciprocal-prime lower bound for x >= 10^8
-- statement:
--   For every real x >= 10^8, the reciprocal-prime sum up to x is at least the Mertens main term minus 4/(log x)^3.
-- source:
--   R. Mawia, Explicit Mertens sums (2017), TME-EMT, Explicit bounds on primes, Art01, section 2.

import Mathlib

namespace TaoFivePrimes
theorem mawia_reciprocal_sum_lower_bound_large (x : ℝ) (hlarge : 10 ^ 8 ≤ x) :
    Real.log (Real.log x) +
        (Real.eulerMascheroniConstant +
          ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) -
        4 / (Real.log x) ^ 3 ≤
      ∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ) := by
  sorry
end TaoFivePrimes
