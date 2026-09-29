-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_high_cert6
-- name    : TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert6
-- status  : Open
-- author  : @lt9
-- created : 2026-09-27T17:33:20.329883+00:00
-- url     : https://prove2.me/theorems/4c7efa49-01c8-4349-9176-5555f09fd01f
-- title:
--   Rosser--Schoenfeld theta lower bound: high range, sieve shard 6
-- statement:
--   Let $\theta(x)=\sum_{p\le x}\log p$ denote the Chebyshev theta function, where $p$ runs over the primes and $\log$ is the natural logarithm.
--
--   For every integer $n$ with $24178658 \le n \le 33451167$,
--
--   $$
--   (n+1)-2\sqrt{n+1}\le \theta(n),
--   $$
--
--   and in addition the accumulated lower bound $A_{6}$ for $\theta$ at the checkpoint $33451168$ satisfies
--
--   $$
--   A_{6}/2^{40}\le \theta(33451168).
--   $$
--
--   This is shard $6$ of the finite endpoint certificate of the high sub-range $10^6\le t\le 10^8$ in Rosser and Schoenfeld's Theorem 19. The Chebyshev theta function is constant on each unit interval $[n,n+1)$, so checking the inequality just below every integer endpoint dominates the corresponding real statement throughout the interval. The certificate evaluates, for a chain of windows of the interval, the exact number of primes and the sum of their offsets above the window start (a bit-parallel sieve over the 1229 primes below $10^4$), converts the logarithm of each prime at the window start into a fixed-point lower bound, and verifies at every checkpoint the exact integer inequality equivalent to $(x+1)-2\sqrt{x+1}\le\theta(x)$. The second conjunct is the quantitative carry that lets the next shard start from a tight lower bound for $\theta$; it is an unconditional finite statement about the primes up to $10^8$.
--
--   **Formalization Note** The range is one of twelve consecutive shards covering $[10^6,10^8]$; the shards are independent except that each imports the quantitative carry of the previous one, and the leaf theorem splits over their ranges.
-- source:
--   J. B. Rosser and L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois Journal of Mathematics 6 (1962), Theorem 19, p. 82, eq. (4.6), https://doi.org/10.1215/ijm/1255631807 (finite integer endpoint certificate, high sub-range 10^6 <= n <= 10^8, sieve shard 6 of 12)

import Mathlib.NumberTheory.Chebyshev

namespace TaoFivePrimes
theorem rosser_schoenfeld_theta_lower_finite_large_high_cert6 (n : Nat) (h1 : 24178658 <= n) (h2 : n <= 33451167) :
    (((n : Real) + 1) - 2 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((36776160404945376298 : Real) / 2 ^ 40 <= Chebyshev.theta (33451168 : Real)) := by sorry
end TaoFivePrimes
