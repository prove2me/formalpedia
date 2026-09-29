-- Prove2me | Theorems.Thm_WeakGoldbach_prime_bracket_gap_lt_4e18
-- name    : WeakGoldbach.prime_bracket_gap_lt_4e18
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T21:24:50.687127+00:00
-- url     : https://prove2.me/theorems/5e22e2f0-4858-4802-9fda-e679041346d8
-- title:
--   Strict prime-gap bracket through the Helfgott-Platt range
-- statement:
--   For every natural number x in the stated range, there are primes p and q with p ? x < q and q ? p < 4�10^18. Consequently q lies strictly inside (x, x + 4�10^18). This isolates the strict prime-gap input needed for the open-window claim.
-- source:
--   H. A. Helfgott and D. J. Platt, Numerical Verification of the Ternary Goldbach Conjecture up to 8.875e30, arXiv:1305.3062v2, sections 3-4 (prime ladder and spacing computation).

import Mathlib

namespace WeakGoldbach
theorem prime_bracket_gap_lt_4e18 (x : Nat)
    (hxl : Nat.le (10 ^ 26) x)
    (hx : Nat.le x (8875694145621773516800000000000 - 4 * 10 ^ 18)) :
    Exists fun p : Nat => Exists fun q : Nat =>
      And (Nat.Prime p) (And (Nat.Prime q) (And (Nat.le p x)
        (And (Nat.lt x q) (Nat.lt (Nat.sub q p) (4 * 10 ^ 18))))) := by
  sorry
end WeakGoldbach
