-- Prove2me | Theorems.Thm_RamareSaouter2003_prime_interval_large_range
-- name    : RamareSaouter2003.prime_interval_large_range
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T12:04:14.576111+00:00
-- url     : https://prove2.me/theorems/2df65dd3-9767-40ee-a47c-6c3fce84c1f3
-- title:
--   Ramare-Saouter analytic prime interval above 10^20
-- statement:
--   For every real x at least 10^20, the interval (x(1 - 1/81,353,847), x] contains a prime. This is the log(x0)=46 instance of the analytic Theorem 2, weakened to the threshold 10^20.
-- source:
--   Olivier Ramare and Yannick Saouter, Short effective intervals containing primes, Journal of Number Theory 98 (2003), pp. 10-33, https://ramare-olivier.github.io/Maths/gap.pdf, pp. 11-12, Table 1 (log x0 = 46) and Theorem 2.

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic

namespace RamareSaouter2003

theorem prime_interval_large_range (x : ℝ) (hx : 10 ^ (20 : ℕ) ≤ x) :
    ∃ p : ℕ, p.Prime ∧ x * (1 - 1 / 81353847) < (p : ℝ) ∧ (p : ℝ) ≤ x := by
  sorry

end RamareSaouter2003
