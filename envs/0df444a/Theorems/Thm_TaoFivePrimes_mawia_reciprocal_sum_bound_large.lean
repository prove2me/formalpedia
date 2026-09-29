-- Prove2me | Theorems.Thm_TaoFivePrimes_mawia_reciprocal_sum_bound_large
-- name    : TaoFivePrimes.mawia_reciprocal_sum_bound_large
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T12:38:39.495895+00:00
-- url     : https://prove2.me/theorems/c2251fec-2b57-4598-90ec-d9e65cd88d79
-- title:
--   Mawia reciprocal sum bound for x ≥ 10⁸
-- statement:
--   Prove Mawia explicit reciprocal-prime estimate for all $x ≥ 10^8$. This is the large-range analytic component of the full-range estimate.
-- source:
--   R. Mawia, Explicit Mertens sums (2017), TME-EMT, Explicit bounds on primes, Art01, section 2.

import Mathlib

namespace TaoFivePrimes
theorem mawia_reciprocal_sum_bound_large (x : ℝ) (hlarge : 10 ^ 8 ≤ x) :
    |(∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) - Real.log (Real.log x) -
        (Real.eulerMascheroniConstant +
          ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)))| ≤
      4 / (Real.log x) ^ 3 := by
  sorry
end TaoFivePrimes
