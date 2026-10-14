-- Prove2me | Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_sgrp4
-- name    : RamareSaouter2003.prime_interval_nat_ladder_sgrp4
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-13T16:35:30.072236+00:00
-- url     : https://prove2.me/theorems/0c257b7b-aed4-4ab8-80be-5692cb48248c
-- title:
--   Short prime intervals, ladder super-group 4 of 4
-- statement:
--   For every natural number $n$ with
--
--   $$
--   286750217619026779 < n \le 10^{20},
--   $$
--
--   there is a prime $p$ with
--
--   $$
--   n\left(1-\frac{1}{28{,}314{,}000}\right) < p < n.
--   $$
--
--   Role: super-group 4 of 4 of the finite range 10726905041 < n <= 10^20 of the parent `RamareSaouter2003.prime_interval_finite_range_nat_strict_upper`; the super-groups meet end to end and each is proved from 44 consecutive groups (groups 133 to 176 of 176, chunks 6601 to 8766 of 8766).
--
--   **Formalization Note** The statement is the parent's natural-number form (`RamareSaouter2003.prime_interval_finite_range_nat_strict_upper`) restricted to the given range; the endpoints are primes of the certificate ladder.
-- source:
--   Olivier Ramare and Yannick Saouter, Short effective intervals containing primes, Journal of Number Theory 98 (2003), pp. 10-33, Theorem 3 and Section 7 (computational range), https://ramare-olivier.github.io/Maths/gap.pdf (the source of the parent node). Finite verification of the range 10726905041 < n <= 10^20 by a ladder of primes certified with Pocklington's criterion (H. C. Pocklington, Proc. Cambridge Philos. Soc. 18 (1914), 29-30)

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic

namespace RamareSaouter2003

theorem prime_interval_nat_ladder_sgrp4 (n : Nat)
    (hn : 286750217619026779 < n) (hupper : n <= 10 ^ (20 : Nat)) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by sorry

end RamareSaouter2003
