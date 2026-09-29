-- Prove2me | Theorems.Thm_RamareSaouter2003_prime_interval_finite_range_nat_strict_upper
-- name    : RamareSaouter2003.prime_interval_finite_range_nat_strict_upper
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T13:00:04.937224+00:00
-- url     : https://prove2.me/theorems/e04af572-e44a-42cc-bed1-1165bb70ac37
-- title:
--   Strictly internal natural interval certificate for the finite range
-- statement:
--   For each natural endpoint n in the finite computational range, there is a prime strictly below n and above n(1 - 1/28,314,000). This natural endpoint form is the finite certificate used after rounding an arbitrary real x upward to floor(x)+1.
-- source:
--   Olivier Ramare and Yannick Saouter, Short effective intervals containing primes, Journal of Number Theory 98 (2003), pp. 10-33, Theorem 3 and Section 7 (computational range), https://ramare-olivier.github.io/Maths/gap.pdf

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic

namespace RamareSaouter2003

theorem prime_interval_finite_range_nat_strict_upper (n : Nat)
    (hn : 10726905041 < n) (hupper : n <= 10 ^ (20 : Nat)) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  sorry

end RamareSaouter2003
