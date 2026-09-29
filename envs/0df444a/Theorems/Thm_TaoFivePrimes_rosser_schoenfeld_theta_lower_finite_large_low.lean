-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_low
-- name    : TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_low
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-25T14:25:39.666323+00:00
-- url     : https://prove2.me/theorems/85c8b463-e2b2-4eaf-a6cc-de710dd09cdf
-- title:
--   Rosser-Schoenfeld theta lower bound: low interval
-- statement:
--   For every real number $t$ in $1423 \le t \le 10^4, the Chebyshev theta function satisfies
--
--   $$t - 2\\sqrt{t} < \\theta(t).$$
--
--   This is the range-restricted form of the finite estimate in Rosser and Schoenfeld Theorem 19.
-- source:
--   J. B. Rosser and L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois Journal of Mathematics 6 (1962), Theorem 19, p. 82, eq. (4.6), https://doi.org/10.1215/ijm/1255631807

import Mathlib.NumberTheory.Chebyshev

namespace TaoFivePrimes
theorem rosser_schoenfeld_theta_lower_finite_large_low (t : Real) (h1 : 1423 <= t) (h2 : t <= 10 ^ 4) :
    t - 2 * Real.sqrt t < Chebyshev.theta t := by sorry
end TaoFivePrimes
