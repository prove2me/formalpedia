-- Prove2me | Theorems.Thm_WeakGoldbach_prime_bracket_gap_lt_4e18_upper_range
-- name    : WeakGoldbach.prime_bracket_gap_lt_4e18_upper_range
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T22:21:06.080412+00:00
-- url     : https://prove2.me/theorems/4cc9ed73-8155-4bd2-b095-fe4372315885
-- title:
--   Prime brackets in the upper Helfgott-Platt range
-- statement:
--   For every integer x from 105000000000000000000000001 through 8875694145621773516800000000000 - 4�10^18, there are primes p ? x < q whose difference is less than 4�10^18. This is the upper-range computational part of the prime-spacing assertion.
-- source:
--   H. A. Helfgott and D. J. Platt, Numerical Verification of the Ternary Goldbach Conjecture up to 8.875e30, arXiv:1305.3062v2, sections 3-4 (prime ladder and spacing computation); upper-range restriction of WeakGoldbach.prime_bracket_gap_lt_4e18.

import Mathlib

namespace WeakGoldbach
theorem prime_bracket_gap_lt_4e18_upper_range (x : Nat)
    (hxl : Nat.le (105000000000000000000000001) x)
    (hx : Nat.le x (8875694145621773516800000000000 - 4 * 10 ^ 18)) :
    Exists fun p : Nat => Exists fun q : Nat =>
      And (Nat.Prime p) (And (Nat.Prime q) (And (Nat.le p x)
        (And (Nat.lt x q) (Nat.lt (Nat.sub q p) (4 * 10 ^ 18))))) := by
  sorry
end WeakGoldbach
