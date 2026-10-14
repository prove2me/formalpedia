-- Prove2me | Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03724
-- name    : RamareSaouter2003.prime_interval_nat_ladder_c03724
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-12T05:49:17.102371+00:00
-- url     : https://prove2.me/theorems/6f957d8e-09d6-4fcf-adcb-e36e4a1cfbee
-- title:
--   Short prime intervals, ladder chunk 3724 of 8766
-- statement:
--   For every natural number $n$ with
--
--   $$
--   90615690043477 < n \le 90839939968397,
--   $$
--
--   there is a prime $p$ with
--
--   $$
--   n\left(1-\frac{1}{28{,}314{,}000}\right) < p < n.
--   $$
--
--   Role: chunk 3724 of 8766 (group 75 of 176) of the finite range 10726905041 < n <= 10^20 of the parent `RamareSaouter2003.prime_interval_finite_range_nat_strict_upper`; consecutive chunks meet end to end.
--
--   **Formalization Note** The statement is the parent's natural-number form (`RamareSaouter2003.prime_interval_finite_range_nat_strict_upper`) restricted to the given range; the endpoints are primes of the certificate ladder.
-- source:
--   Olivier Ramare and Yannick Saouter, Short effective intervals containing primes, Journal of Number Theory 98 (2003), pp. 10-33, Theorem 3 and Section 7 (computational range), https://ramare-olivier.github.io/Maths/gap.pdf (the source of the parent node). Finite verification of the range 10726905041 < n <= 10^20 by a ladder of primes certified with Pocklington's criterion (H. C. Pocklington, Proc. Cambridge Philos. Soc. 18 (1914), 29-30)

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic

namespace RamareSaouter2003

theorem prime_interval_nat_ladder_c03724 (n : Nat)
    (hn : 90615690043477 < n) (hupper : n <= 90839939968397) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by sorry

end RamareSaouter2003
