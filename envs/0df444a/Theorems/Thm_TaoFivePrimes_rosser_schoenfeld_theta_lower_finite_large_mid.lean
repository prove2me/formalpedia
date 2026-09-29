-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_mid
-- name    : TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_mid
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-25T14:25:38.106376+00:00
-- url     : https://prove2.me/theorems/124879d5-5961-41b5-bd97-f09c8cd50be8
-- title:
--   Rosser-Schoenfeld theta lower bound: mid interval
-- statement:
--   For every real number $t$ in $10^4 \le t \le 10^6, the Chebyshev theta function satisfies
--
--   $$t - 2\\sqrt{t} < \\theta(t).$$
--
--   This is the range-restricted form of the finite estimate in Rosser and Schoenfeld Theorem 19.
-- source:
--   J. B. Rosser and L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois Journal of Mathematics 6 (1962), Theorem 19, p. 82, eq. (4.6), https://doi.org/10.1215/ijm/1255631807

import Mathlib.NumberTheory.Chebyshev

namespace TaoFivePrimes
theorem rosser_schoenfeld_theta_lower_finite_large_mid (t : Real) (h1 : 10 ^ 4 <= t) (h2 : t <= 10 ^ 6) :
    t - 2 * Real.sqrt t < Chebyshev.theta t := by sorry
end TaoFivePrimes
