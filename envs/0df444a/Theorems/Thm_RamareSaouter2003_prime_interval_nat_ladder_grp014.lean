-- Prove2me | Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp014
-- name    : RamareSaouter2003.prime_interval_nat_ladder_grp014
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-10T21:22:30.861491+00:00
-- url     : https://prove2.me/theorems/8904b432-bd4d-44d9-86d9-c2a360c714b2
-- title:
--   Short prime intervals, ladder group 14 of 176
-- statement:
--   For every natural number $n$ with
--
--   $$
--   45340845131 < n \le 50809618939,
--   $$
--
--   there is a prime $p$ with
--
--   $$
--   n\left(1-\frac{1}{28{,}314{,}000}\right) < p < n.
--   $$
--
--   Role: group 14 of 176 of the finite range 10726905041 < n <= 10^20 of the parent `RamareSaouter2003.prime_interval_finite_range_nat_strict_upper`; the groups meet end to end and each is proved from its 50 consecutive ladder chunks (chunks 651 to 700 of 8766).
--
--   **Formalization Note** The statement is the parent's natural-number form (`RamareSaouter2003.prime_interval_finite_range_nat_strict_upper`) restricted to the given range; the endpoints are primes of the certificate ladder.
-- source:
--   Olivier Ramare and Yannick Saouter, Short effective intervals containing primes, Journal of Number Theory 98 (2003), pp. 10-33, Theorem 3 and Section 7 (computational range), https://ramare-olivier.github.io/Maths/gap.pdf (the source of the parent node). Finite verification of the range 10726905041 < n <= 10^20 by a ladder of primes certified with Pocklington's criterion (H. C. Pocklington, Proc. Cambridge Philos. Soc. 18 (1914), 29-30)

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic

namespace RamareSaouter2003

theorem prime_interval_nat_ladder_grp014 (n : Nat)
    (hn : 45340845131 < n) (hupper : n <= 50809618939) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by sorry

end RamareSaouter2003
