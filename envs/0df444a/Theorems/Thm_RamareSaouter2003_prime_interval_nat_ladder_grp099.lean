-- Prove2me | Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp099
-- name    : RamareSaouter2003.prime_interval_nat_ladder_grp099
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-12T13:15:17.273984+00:00
-- url     : https://prove2.me/theorems/02432578-a66a-4a36-867d-19fdd8064fc2
-- title:
--   Short prime intervals, ladder group 99 of 176
-- statement:
--   For every natural number $n$ with
--
--   $$
--   2345869641159829 < n \le 2701984647071959,
--   $$
--
--   there is a prime $p$ with
--
--   $$
--   n\left(1-\frac{1}{28{,}314{,}000}\right) < p < n.
--   $$
--
--   Role: group 99 of 176 of the finite range 10726905041 < n <= 10^20 of the parent `RamareSaouter2003.prime_interval_finite_range_nat_strict_upper`; the groups meet end to end and each is proved from its 50 consecutive ladder chunks (chunks 4901 to 4950 of 8766).
--
--   **Formalization Note** The statement is the parent's natural-number form (`RamareSaouter2003.prime_interval_finite_range_nat_strict_upper`) restricted to the given range; the endpoints are primes of the certificate ladder.
-- source:
--   Olivier Ramare and Yannick Saouter, Short effective intervals containing primes, Journal of Number Theory 98 (2003), pp. 10-33, Theorem 3 and Section 7 (computational range), https://ramare-olivier.github.io/Maths/gap.pdf (the source of the parent node). Finite verification of the range 10726905041 < n <= 10^20 by a ladder of primes certified with Pocklington's criterion (H. C. Pocklington, Proc. Cambridge Philos. Soc. 18 (1914), 29-30)

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic

namespace RamareSaouter2003

theorem prime_interval_nat_ladder_grp099 (n : Nat)
    (hn : 2345869641159829 < n) (hupper : n <= 2701984647071959) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by sorry

end RamareSaouter2003
