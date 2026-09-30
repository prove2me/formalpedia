-- Prove2me | Theorems.Thm_TaoFivePrimes_mawia_reciprocal_sum_upper_bound_small
-- name    : TaoFivePrimes.mawia_reciprocal_sum_upper_bound_small
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-25T14:25:25.811985+00:00
-- url     : https://prove2.me/theorems/6b4f23b2-12ba-40f0-b27c-5dffd48976e1
-- title:
--   Mawia small-range reciprocal-prime upper bound
-- statement:
--   For every real x with 2 ≤ x ≤ 10^8, the reciprocal-prime sum through x is at most the logarithmic main term plus the Meissel–Mertens constant and 4/(log x)^3.
-- source:
--   R. Mawia, “Explicit estimates for some summatory functions of primes,” Integers 17 (2017), Theorem 10.12.30 (Mawia reciprocal-prime estimate; source given on the parent theorem as section 2).

import Mathlib

namespace TaoFivePrimes
theorem mawia_reciprocal_sum_upper_bound_small (x : ℝ) (hx : 2 ≤ x) (hsmall : x ≤ 10 ^ 8) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) ≤
      Real.log (Real.log x) +
        (Real.eulerMascheroniConstant +
          ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) +
        4 / (Real.log x) ^ 3 := by
  sorry
end TaoFivePrimes
