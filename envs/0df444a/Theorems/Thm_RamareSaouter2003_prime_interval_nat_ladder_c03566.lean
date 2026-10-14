-- Prove2me | Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03566
-- name    : RamareSaouter2003.prime_interval_nat_ladder_c03566
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-12T05:00:34.93285+00:00
-- url     : https://prove2.me/theorems/cb155af6-c06f-4188-8b18-65d7c7591ca3
-- title:
--   Short prime intervals, ladder chunk 3566 of 8766
-- statement:
--   For every natural number $n$ with
--
--   $$
--   61319756835331 < n \le 61471507054987,
--   $$
--
--   there is a prime $p$ with
--
--   $$
--   n\left(1-\frac{1}{28{,}314{,}000}\right) < p < n.
--   $$
--
--   Role: chunk 3566 of 8766 (group 72 of 176) of the finite range 10726905041 < n <= 10^20 of the parent `RamareSaouter2003.prime_interval_finite_range_nat_strict_upper`; consecutive chunks meet end to end.
--
--   **Formalization Note** The statement is the parent's natural-number form (`RamareSaouter2003.prime_interval_finite_range_nat_strict_upper`) restricted to the given range; the endpoints are primes of the certificate ladder.
-- source:
--   Olivier Ramare and Yannick Saouter, Short effective intervals containing primes, Journal of Number Theory 98 (2003), pp. 10-33, Theorem 3 and Section 7 (computational range), https://ramare-olivier.github.io/Maths/gap.pdf (the source of the parent node). Finite verification of the range 10726905041 < n <= 10^20 by a ladder of primes certified with Pocklington's criterion (H. C. Pocklington, Proc. Cambridge Philos. Soc. 18 (1914), 29-30)

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic

namespace RamareSaouter2003

theorem prime_interval_nat_ladder_c03566 (n : Nat)
    (hn : 61319756835331 < n) (hupper : n <= 61471507054987) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by sorry

end RamareSaouter2003
