-- Prove2me | Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05530
-- name    : RamareSaouter2003.prime_interval_nat_ladder_c05530
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-12T16:31:19.113992+00:00
-- url     : https://prove2.me/theorems/4e614950-92a7-48d5-98c6-379dc33fe457
-- title:
--   Short prime intervals, ladder chunk 5530 of 8766
-- statement:
--   For every natural number $n$ with
--
--   $$
--   13883984024041303 < n \le 13923293132301961,
--   $$
--
--   there is a prime $p$ with
--
--   $$
--   n\left(1-\frac{1}{28{,}314{,}000}\right) < p < n.
--   $$
--
--   Role: chunk 5530 of 8766 (group 111 of 176) of the finite range 10726905041 < n <= 10^20 of the parent `RamareSaouter2003.prime_interval_finite_range_nat_strict_upper`; consecutive chunks meet end to end.
--
--   **Formalization Note** The statement is the parent's natural-number form (`RamareSaouter2003.prime_interval_finite_range_nat_strict_upper`) restricted to the given range; the endpoints are primes of the certificate ladder.
-- source:
--   Olivier Ramare and Yannick Saouter, Short effective intervals containing primes, Journal of Number Theory 98 (2003), pp. 10-33, Theorem 3 and Section 7 (computational range), https://ramare-olivier.github.io/Maths/gap.pdf (the source of the parent node). Finite verification of the range 10726905041 < n <= 10^20 by a ladder of primes certified with Pocklington's criterion (H. C. Pocklington, Proc. Cambridge Philos. Soc. 18 (1914), 29-30)

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic

namespace RamareSaouter2003

theorem prime_interval_nat_ladder_c05530 (n : Nat)
    (hn : 13883984024041303 < n) (hupper : n <= 13923293132301961) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by sorry

end RamareSaouter2003
