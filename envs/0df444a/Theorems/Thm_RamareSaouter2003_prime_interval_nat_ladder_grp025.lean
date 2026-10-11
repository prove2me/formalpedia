-- Prove2me | Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp025
-- name    : RamareSaouter2003.prime_interval_nat_ladder_grp025
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-11T04:17:13.604791+00:00
-- url     : https://prove2.me/theorems/55f147a7-f0bb-4870-b243-336da7e732f3
-- title:
--   Short prime intervals, ladder group 25 of 176
-- statement:
--   For every natural number $n$ with
--
--   $$
--   166837303537 < n \le 189054413519,
--   $$
--
--   there is a prime $p$ with
--
--   $$
--   n\left(1-\frac{1}{28{,}314{,}000}\right) < p < n.
--   $$
--
--   Role: group 25 of 176 of the finite range 10726905041 < n <= 10^20 of the parent `RamareSaouter2003.prime_interval_finite_range_nat_strict_upper`; the groups meet end to end and each is proved from its 50 consecutive ladder chunks (chunks 1201 to 1250 of 8766).
--
--   **Formalization Note** The statement is the parent's natural-number form (`RamareSaouter2003.prime_interval_finite_range_nat_strict_upper`) restricted to the given range; the endpoints are primes of the certificate ladder.
-- source:
--   Olivier Ramare and Yannick Saouter, Short effective intervals containing primes, Journal of Number Theory 98 (2003), pp. 10-33, Theorem 3 and Section 7 (computational range), https://ramare-olivier.github.io/Maths/gap.pdf (the source of the parent node). Finite verification of the range 10726905041 < n <= 10^20 by a ladder of primes certified with Pocklington's criterion (H. C. Pocklington, Proc. Cambridge Philos. Soc. 18 (1914), 29-30)

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic

namespace RamareSaouter2003

theorem prime_interval_nat_ladder_grp025 (n : Nat)
    (hn : 166837303537 < n) (hupper : n <= 189054413519) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by sorry

end RamareSaouter2003
