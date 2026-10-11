-- Prove2me | Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01154
-- name    : RamareSaouter2003.prime_interval_nat_ladder_c01154
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-11T03:05:19.588085+00:00
-- url     : https://prove2.me/theorems/fc79dfaa-33c1-40fc-992f-ce5e63d713fc
-- title:
--   Short prime intervals, ladder chunk 1154 of 8766
-- statement:
--   For every natural number $n$ with
--
--   $$
--   148359264541 < n \le 148730055581,
--   $$
--
--   there is a prime $p$ with
--
--   $$
--   n\left(1-\frac{1}{28{,}314{,}000}\right) < p < n.
--   $$
--
--   Role: chunk 1154 of 8766 (group 24 of 176) of the finite range 10726905041 < n <= 10^20 of the parent `RamareSaouter2003.prime_interval_finite_range_nat_strict_upper`; consecutive chunks meet end to end.
--
--   **Formalization Note** The statement is the parent's natural-number form (`RamareSaouter2003.prime_interval_finite_range_nat_strict_upper`) restricted to the given range; the endpoints are primes of the certificate ladder.
-- source:
--   Olivier Ramare and Yannick Saouter, Short effective intervals containing primes, Journal of Number Theory 98 (2003), pp. 10-33, Theorem 3 and Section 7 (computational range), https://ramare-olivier.github.io/Maths/gap.pdf (the source of the parent node). Finite verification of the range 10726905041 < n <= 10^20 by a ladder of primes certified with Pocklington's criterion (H. C. Pocklington, Proc. Cambridge Philos. Soc. 18 (1914), 29-30)

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic

namespace RamareSaouter2003

theorem prime_interval_nat_ladder_c01154 (n : Nat)
    (hn : 148359264541 < n) (hupper : n <= 148730055581) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by sorry

end RamareSaouter2003
