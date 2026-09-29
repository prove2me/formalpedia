-- Prove2me | Theorems.Thm_TaoFivePrimes_mawia_reciprocal_sum_bound_small
-- name    : TaoFivePrimes.mawia_reciprocal_sum_bound_small
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T12:38:39.11406+00:00
-- url     : https://prove2.me/theorems/70923020-40bf-4804-b3e7-0741decba521
-- title:
--   Mawia reciprocal sum bound for 2 ≤ x ≤ 10⁸
-- statement:
--   Prove Mawia explicit reciprocal-prime estimate on the bounded initial interval $2 ≤ x ≤ 10^8$. This is the finite-range component of the full-range estimate.
-- source:
--   R. Mawia, Explicit Mertens sums (2017), TME-EMT, Explicit bounds on primes, Art01, section 2.

import Mathlib

namespace TaoFivePrimes
theorem mawia_reciprocal_sum_bound_small (x : ℝ) (hx : 2 ≤ x) (hsmall : x ≤ 10 ^ 8) :
    |(∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) - Real.log (Real.log x) -
        (Real.eulerMascheroniConstant +
          ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)))| ≤
      4 / (Real.log x) ^ 3 := by
  sorry
end TaoFivePrimes
