-- Prove2me | Theorems.Thm_TaoFivePrimes_mawia_reciprocal_sum_upper_bound_large
-- name    : TaoFivePrimes.mawia_reciprocal_sum_upper_bound_large
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T13:55:58.119891+00:00
-- url     : https://prove2.me/theorems/aa0abc75-04a9-4ea9-9da2-f9f65e75ac86
-- title:
--   Mawia reciprocal-prime upper bound for x >= 10^8
-- statement:
--   For every real x >= 10^8, the reciprocal-prime sum up to x is at most the Mertens main term plus 4/(log x)^3.
-- source:
--   R. Mawia, Explicit Mertens sums (2017), TME-EMT, Explicit bounds on primes, Art01, section 2.

import Mathlib

namespace TaoFivePrimes
theorem mawia_reciprocal_sum_upper_bound_large (x : ℝ) (hlarge : 10 ^ 8 ≤ x) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) ≤
      Real.log (Real.log x) +
        (Real.eulerMascheroniConstant +
          ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) +
        4 / (Real.log x) ^ 3 := by
  sorry
end TaoFivePrimes
