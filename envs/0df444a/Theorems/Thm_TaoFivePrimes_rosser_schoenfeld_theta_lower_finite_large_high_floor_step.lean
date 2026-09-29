-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_high_floor_step
-- name    : TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_floor_step
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-27T13:10:15.93309+00:00
-- url     : https://prove2.me/theorems/ad21354f-32fa-44ff-9709-c0db20752151
-- title:
--   Rosser--Schoenfeld theta lower bound: high range, analytic floor step
-- statement:
--   Let $\theta(x)=\sum_{p\le x}\log p$ denote the Chebyshev theta function, where $p$ ranges over the primes and $\log$ is the natural logarithm, and let $\lfloor t\rfloor$ be the integer part of a real number $t$.
--
--   For every real $t$ with $10^6 \le t \le 10^8$,
--
--   $$
--   t-2\sqrt{t} < \bigl(\lfloor t\rfloor+1\bigr)-2\sqrt{\lfloor t\rfloor+1}.
--   $$
--
--   This is the analytic monotonicity step that reduces the real range $10^6\le t\le 10^8$ of the finite Rosser--Schoenfeld estimate to integer inputs. The map $x\mapsto x-2\sqrt{x}$ is strictly increasing on $[1,\infty)$, and $t$ is strictly smaller than the next integer $\lfloor t\rfloor+1$, which is the right endpoint of the unit interval containing $t$. Hence $t-2\sqrt t$ is strictly dominated by the value of the same expression at that endpoint. Combined with the integer endpoint certificate on the same range, this gives $t-2\sqrt{t}<\theta(t)$ for all real $t$ in the range, the finite lower bound of Rosser and Schoenfeld's Theorem 19.
--
--   **Formalization Note** The upper hypothesis $t\le 10^8$ is not used by the argument; it is retained so that the statement matches the range of the parent target.
-- source:
--   J. B. Rosser and L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois Journal of Mathematics 6 (1962), Theorem 19, p. 82, eq. (4.6), https://doi.org/10.1215/ijm/1255631807 (analytic monotonicity reduction step for the finite range 10^6 <= t <= 10^8)

import Mathlib.NumberTheory.Chebyshev

namespace TaoFivePrimes
theorem rosser_schoenfeld_theta_lower_finite_large_high_floor_step (t : Real) (h1 : 10 ^ 6 <= t) (h2 : t <= 10 ^ 8) :
    t - 2 * Real.sqrt t < ((Nat.floor t : Real) + 1) - 2 * Real.sqrt ((Nat.floor t : Real) + 1) := by sorry
end TaoFivePrimes
