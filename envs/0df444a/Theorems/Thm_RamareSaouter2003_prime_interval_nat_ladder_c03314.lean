-- Prove2me | Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03314
-- name    : RamareSaouter2003.prime_interval_nat_ladder_c03314
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-12T02:57:20.955475+00:00
-- url     : https://prove2.me/theorems/01d40f54-5536-4929-aa2f-8f91b3688118
-- title:
--   Short prime intervals, ladder chunk 3314 of 8766
-- statement:
--   For every natural number $n$ with
--
--   $$
--   32892312560203 < n \le 32973712355489,
--   $$
--
--   there is a prime $p$ with
--
--   $$
--   n\left(1-\frac{1}{28{,}314{,}000}\right) < p < n.
--   $$
--
--   Role: chunk 3314 of 8766 (group 67 of 176) of the finite range 10726905041 < n <= 10^20 of the parent `RamareSaouter2003.prime_interval_finite_range_nat_strict_upper`; consecutive chunks meet end to end.
--
--   **Formalization Note** The statement is the parent's natural-number form (`RamareSaouter2003.prime_interval_finite_range_nat_strict_upper`) restricted to the given range; the endpoints are primes of the certificate ladder.
-- source:
--   Olivier Ramare and Yannick Saouter, Short effective intervals containing primes, Journal of Number Theory 98 (2003), pp. 10-33, Theorem 3 and Section 7 (computational range), https://ramare-olivier.github.io/Maths/gap.pdf (the source of the parent node). Finite verification of the range 10726905041 < n <= 10^20 by a ladder of primes certified with Pocklington's criterion (H. C. Pocklington, Proc. Cambridge Philos. Soc. 18 (1914), 29-30)

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic

namespace RamareSaouter2003

theorem prime_interval_nat_ladder_c03314 (n : Nat)
    (hn : 32892312560203 < n) (hupper : n <= 32973712355489) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by sorry

end RamareSaouter2003
