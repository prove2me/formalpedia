-- Prove2me | Theorems.Thm_RamareSaouter2003_weighted_interval_mass_gt_one
-- name    : RamareSaouter2003.weighted_interval_mass_gt_one
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T12:41:33.002285+00:00
-- url     : https://prove2.me/theorems/62d19cef-f912-416f-b75b-c2eb5fef4bad
-- title:
--   Ramare-Saouter weighted prime mass bound
-- statement:
--   For every real x >= 10^20, the sum of log p over primes p in (x(1 - 1/81,353,847), x] exceeds 1. This quantitative weighted-count estimate is the analytic step behind the positivity criterion in Theorem 2.
-- source:
--   O. Ramare and Y. Saouter, Short effective intervals containing primes, Journal of Number Theory 98 (2003), pp. 16-20, Theorem 4 specialized using the log x0 = 46 parameter row in Table 1; https://ramare-olivier.github.io/Maths/gap.pdf

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace RamareSaouter2003

theorem weighted_interval_mass_gt_one (x : Real)
    (hx : (10 : Real) ^ (20 : Nat) <= x) :
    1 < Finset.sum (Finset.range (Nat.floor x + 1))
      (fun p => if p.Prime /\ x * (1 - 1 / 81353847) < (p : Real) /\ (p : Real) <= x
        then Real.log (p : Real) else 0) := by
  sorry

end RamareSaouter2003
