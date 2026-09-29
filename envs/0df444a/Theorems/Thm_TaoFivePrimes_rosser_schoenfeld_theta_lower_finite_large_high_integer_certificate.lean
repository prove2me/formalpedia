-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_high_integer_certificate
-- name    : TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_integer_certificate
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-27T13:10:17.07144+00:00
-- url     : https://prove2.me/theorems/46df5d5d-d0e9-4bc9-834c-91cfd97d047e
-- title:
--   Rosser--Schoenfeld theta lower bound: high range, integer endpoint certificate
-- statement:
--   Let $\theta(x)=\sum_{p\le x}\log p$ denote the Chebyshev theta function, where $p$ ranges over the primes and $\log$ is the natural logarithm.
--
--   For every integer $n$ with $10^6 \le n \le 10^8$,
--
--   $$
--   (n+1)-2\sqrt{n+1}\le \theta(n).
--   $$
--
--   This is the finite endpoint certificate of the high sub-range $10^6\le t\le 10^8$ in Rosser and Schoenfeld's Theorem 19. The Chebyshev theta function is constant on each unit interval $[n,n+1)$, so checking the inequality at the right endpoint $n+1$ of every such interval dominates the corresponding real statement throughout the interval. It is an unconditional finite statement about the primes up to $10^8$: it asserts that the sum of $\log p$ over all primes $p\le n$ stays above the linear expression $(n+1)-2\sqrt{n+1}$ with the stated margin.
--
--   **Formalization Note** The margin is comfortably large throughout the range (about $1.6\times10^3$ at $n=10^6$ and about $2\times10^4$ at $n=10^8$), so the statement is a finite verification rather than an asymptotic estimate.
-- source:
--   J. B. Rosser and L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois Journal of Mathematics 6 (1962), Theorem 19, p. 82, eq. (4.6), https://doi.org/10.1215/ijm/1255631807 (finite integer endpoint certificate, high sub-range 10^6 <= n <= 10^8)

import Mathlib.NumberTheory.Chebyshev

namespace TaoFivePrimes
theorem rosser_schoenfeld_theta_lower_finite_large_high_integer_certificate (n : Nat) (h1 : 10 ^ 6 <= n) (h2 : n <= 10 ^ 8) :
    ((n : Real) + 1) - 2 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta n := by sorry
end TaoFivePrimes
