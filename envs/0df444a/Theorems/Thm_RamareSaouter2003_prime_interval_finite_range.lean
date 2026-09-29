-- Prove2me | Theorems.Thm_RamareSaouter2003_prime_interval_finite_range
-- name    : RamareSaouter2003.prime_interval_finite_range
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T12:04:13.730393+00:00
-- url     : https://prove2.me/theorems/bd3e60ec-3dbe-4c9b-a1d2-fdfee7f1a7b7
-- title:
--   Ramare-Saouter finite-range prime interval certificate
-- statement:
--   For every real x strictly above 10,726,905,041 and below 10^20, the interval (x(1 - 1/28,314,000), x] contains a prime. This isolates the computational prime-generation and certificate range used in the proof of Theorem 3.
-- source:
--   Olivier Ramare and Yannick Saouter, Short effective intervals containing primes, Journal of Number Theory 98 (2003), pp. 10-33, https://ramare-olivier.github.io/Maths/gap.pdf, pp. 12-13, Theorem 3 and pp. 27-31, Section 7 (computational range).

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic

namespace RamareSaouter2003

theorem prime_interval_finite_range (x : ℝ)
    (hx : 10726905041 < x) (hupper : x < 10 ^ (20 : ℕ)) :
    ∃ p : ℕ, p.Prime ∧ x * (1 - 1 / 28314000) < (p : ℝ) ∧ (p : ℝ) ≤ x := by
  sorry

end RamareSaouter2003
