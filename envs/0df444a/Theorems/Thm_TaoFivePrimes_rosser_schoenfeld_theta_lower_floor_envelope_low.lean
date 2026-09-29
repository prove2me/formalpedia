-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_floor_envelope_low
-- name    : TaoFivePrimes.rosser_schoenfeld_theta_lower_floor_envelope_low
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-25T14:06:30.688944+00:00
-- url     : https://prove2.me/theorems/1e2c9949-37c4-4010-b712-9ec6fe14e265
-- title:
--   Monotone floor envelope for the Rosser-Schoenfeld expression
-- statement:
--   For each real input t in the low range, the Rosser-Schoenfeld expression at t is bounded above by its value at the next integer, the right endpoint of the interval on which Chebyshev theta is constant. This is the analytic monotonicity step in reducing the real range to integer endpoint certificates.
-- source:
--   Analytic reduction step for Rosser and Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois Journal of Mathematics 6 (1962), Theorem 4, equation (3.14)

import Mathlib.NumberTheory.Chebyshev

import Mathlib.NumberTheory.Chebyshev
namespace TaoFivePrimes
theorem rosser_schoenfeld_theta_lower_floor_envelope_low (t : Real) (h1 : 1420 <= t) (h2 : t <= 10 ^ 4) :
    t * (1 - 1 / (2 * Real.log t)) <=
      ((Nat.floor t : Real) + 1) * (1 - 1 / (2 * Real.log ((Nat.floor t : Real) + 1))) := by sorry
end TaoFivePrimes
