-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_high
-- name    : TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-25T14:25:38.167753+00:00
-- url     : https://prove2.me/theorems/9d16b426-bc8c-4553-8f0f-0e41d9c1d80a
-- title:
--   Rosser-Schoenfeld theta lower bound: high interval
-- statement:
--   For every real number $t$ in $10^6 \le t \le 10^8, the Chebyshev theta function satisfies
--
--   $$t - 2\\sqrt{t} < \\theta(t).$$
--
--   This is the range-restricted form of the finite estimate in Rosser and Schoenfeld Theorem 19.
-- source:
--   J. B. Rosser and L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois Journal of Mathematics 6 (1962), Theorem 19, p. 82, eq. (4.6), https://doi.org/10.1215/ijm/1255631807

import Mathlib.NumberTheory.Chebyshev

namespace TaoFivePrimes
theorem rosser_schoenfeld_theta_lower_finite_large_high (t : Real) (h1 : 10 ^ 6 <= t) (h2 : t <= 10 ^ 8) :
    t - 2 * Real.sqrt t < Chebyshev.theta t := by sorry
end TaoFivePrimes
