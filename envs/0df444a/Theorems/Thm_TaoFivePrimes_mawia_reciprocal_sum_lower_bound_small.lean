-- Prove2me | Theorems.Thm_TaoFivePrimes_mawia_reciprocal_sum_lower_bound_small
-- name    : TaoFivePrimes.mawia_reciprocal_sum_lower_bound_small
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-25T14:25:27.367978+00:00
-- url     : https://prove2.me/theorems/5cb6180b-3a9f-47fa-ae12-241767b2ba05
-- title:
--   Mawia small-range reciprocal-prime lower bound
-- statement:
--   For every real x with 2 ≤ x ≤ 10^8, the reciprocal-prime sum through x is at least the logarithmic main term plus the Meissel–Mertens constant minus 4/(log x)^3.
-- source:
--   R. Mawia, “Explicit estimates for some summatory functions of primes,” Integers 17 (2017), Theorem 10.12.30 (Mawia reciprocal-prime estimate; source given on the parent theorem as section 2).

import Mathlib

namespace TaoFivePrimes
theorem mawia_reciprocal_sum_lower_bound_small (x : ℝ) (hx : 2 ≤ x) (hsmall : x ≤ 10 ^ 8) :
    Real.log (Real.log x) +
        (Real.eulerMascheroniConstant +
          ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) -
        4 / (Real.log x) ^ 3 ≤
      ∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ) := by
  sorry
end TaoFivePrimes
