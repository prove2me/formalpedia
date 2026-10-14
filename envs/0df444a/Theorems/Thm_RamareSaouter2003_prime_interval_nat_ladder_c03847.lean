-- Prove2me | Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03847
-- name    : RamareSaouter2003.prime_interval_nat_ladder_c03847
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-12T06:50:02.1246+00:00
-- url     : https://prove2.me/theorems/560cf975-6966-4d27-9de2-543a8a5675a9
-- title:
--   Short prime intervals, ladder chunk 3847 of 8766
-- statement:
--   For every natural number $n$ with
--
--   $$
--   122810669821589 < n \le 123114593827213,
--   $$
--
--   there is a prime $p$ with
--
--   $$
--   n\left(1-\frac{1}{28{,}314{,}000}\right) < p < n.
--   $$
--
--   Role: chunk 3847 of 8766 (group 77 of 176) of the finite range 10726905041 < n <= 10^20 of the parent `RamareSaouter2003.prime_interval_finite_range_nat_strict_upper`; consecutive chunks meet end to end.
--
--   **Formalization Note** The statement is the parent's natural-number form (`RamareSaouter2003.prime_interval_finite_range_nat_strict_upper`) restricted to the given range; the endpoints are primes of the certificate ladder.
-- source:
--   Olivier Ramare and Yannick Saouter, Short effective intervals containing primes, Journal of Number Theory 98 (2003), pp. 10-33, Theorem 3 and Section 7 (computational range), https://ramare-olivier.github.io/Maths/gap.pdf (the source of the parent node). Finite verification of the range 10726905041 < n <= 10^20 by a ladder of primes certified with Pocklington's criterion (H. C. Pocklington, Proc. Cambridge Philos. Soc. 18 (1914), 29-30)

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic

namespace RamareSaouter2003

theorem prime_interval_nat_ladder_c03847 (n : Nat)
    (hn : 122810669821589 < n) (hupper : n <= 123114593827213) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by sorry

end RamareSaouter2003
