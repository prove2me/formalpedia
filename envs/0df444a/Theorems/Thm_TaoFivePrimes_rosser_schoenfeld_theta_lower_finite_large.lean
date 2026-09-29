-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large
-- name    : TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-25T14:13:47.548997+00:00
-- url     : https://prove2.me/theorems/f48a0c89-81ec-44a1-a5a0-e213501c24b7
-- title:
--   Rosser-Schoenfeld theta bound: 1423 to 100,000,000
-- statement:
--   For every real number t in the interval $1423 \le t \le 10^8$, the Chebyshev theta function satisfies
--
--   $$t - 2\sqrt{t} < \theta(t).$$
--
--   This is the upper finite range in Rosser and Schoenfeld's Theorem 19; it supplies a stronger lower estimate than the analytic bound used by the parent theorem.
-- source:
--   J. B. Rosser and L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois Journal of Mathematics 6 (1962), Theorem 19, p. 82, eq. (4.6), upper finite range 1423 <= t <= 10^8. https://doi.org/10.1215/ijm/1255631807

import Mathlib.NumberTheory.Chebyshev

namespace TaoFivePrimes
theorem rosser_schoenfeld_theta_lower_finite_large (t : Real) (h1 : 1423 <= t) (h2 : t <= 10 ^ 8) :
    t - 2 * Real.sqrt t < Chebyshev.theta t := by sorry
end TaoFivePrimes
