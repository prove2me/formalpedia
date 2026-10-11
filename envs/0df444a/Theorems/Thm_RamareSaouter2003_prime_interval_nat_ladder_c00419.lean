-- Prove2me | Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00419
-- name    : RamareSaouter2003.prime_interval_nat_ladder_c00419
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-10T17:44:41.819052+00:00
-- url     : https://prove2.me/theorems/40e71550-d196-4da6-a602-5619b73925dc
-- title:
--   Short prime intervals, ladder chunk 419 of 8766
-- statement:
--   For every natural number $n$ with
--
--   $$
--   26840935621 < n \le 26901124039,
--   $$
--
--   there is a prime $p$ with
--
--   $$
--   n\left(1-\frac{1}{28{,}314{,}000}\right) < p < n.
--   $$
--
--   Role: chunk 419 of 8766 (group 9 of 176) of the finite range 10726905041 < n <= 10^20 of the parent `RamareSaouter2003.prime_interval_finite_range_nat_strict_upper`; consecutive chunks meet end to end.
--
--   **Formalization Note** The statement is the parent's natural-number form (`RamareSaouter2003.prime_interval_finite_range_nat_strict_upper`) restricted to the given range; the endpoints are primes of the certificate ladder.
-- source:
--   Olivier Ramare and Yannick Saouter, Short effective intervals containing primes, Journal of Number Theory 98 (2003), pp. 10-33, Theorem 3 and Section 7 (computational range), https://ramare-olivier.github.io/Maths/gap.pdf (the source of the parent node). Finite verification of the range 10726905041 < n <= 10^20 by a ladder of primes certified with Pocklington's criterion (H. C. Pocklington, Proc. Cambridge Philos. Soc. 18 (1914), 29-30)

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic

namespace RamareSaouter2003

theorem prime_interval_nat_ladder_c00419 (n : Nat)
    (hn : 26840935621 < n) (hupper : n <= 26901124039) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by sorry

end RamareSaouter2003
