-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_high_cert208
-- name    : TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert208
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-27T18:21:56.622907+00:00
-- url     : https://prove2.me/theorems/f719d561-1052-472d-aa03-a7716de03f1f
-- title:
--   Rosser--Schoenfeld theta lower bound: high range, sieve shard 8
-- statement:
--   Let $\theta(x)=\sum_{p\le x}\log p$ be the Chebyshev theta function ($p$ prime, $\log$ natural) and suppose the integer $B$ below satisfies $B/2^{40}\le\theta(8833512)$.
--
--   Then for every integer $n$ with $8833512\le n\le11075303$,
--
--   $$
--   (n+1)-2\sqrt{n+1}\le\theta(n),
--   $$
--
--   and moreover the accumulated lower bound $A_{8}$ computed by the certificate satisfies $A_{8}/2^{40}\le\theta(11075304)$.
--
--   This is shard $8$ of the finite endpoint certificate of the high sub-range $10^6\le t\le10^8$ in Rosser and Schoenfeld's Theorem 19, the finite verification at the integer endpoints on which the Chebyshev theta function is constant. The certificate evaluates, for a chain of windows, the exact number of primes and the sum of their offsets above the window start (a bit-parallel sieve over the 1229 primes below $10^4$), converts $\log$ at each window start into a fixed-point lower bound, and checks at every checkpoint the exact integer inequality equivalent to $(x+1)-2\sqrt{x+1}\le\theta(x)$. The hypothesis is the quantitative carry produced by the previous shard, which is what lets this shard start from a tight lower bound for $\theta$; the second conjunct is the carry it hands on. Both conjuncts are unconditional finite statements about the primes up to $10^8$.
--
--   **Formalization Note** The range is one of twelve consecutive shards covering $[10^6,10^8]$; the shards are independent Lean files (the previous carry enters as a hypothesis) and the leaf theorem chains them and splits over their ranges.
-- source:
--   J. B. Rosser and L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois Journal of Mathematics 6 (1962), Theorem 19, p. 82, eq. (4.6), https://doi.org/10.1215/ijm/1255631807 (finite integer endpoint certificate, high sub-range 10^6 <= n <= 10^8, sieve shard 8 of 30)

import Mathlib.NumberTheory.Chebyshev

namespace TaoFivePrimes
theorem rosser_schoenfeld_theta_lower_finite_large_high_cert208
    (hbase : (9710016230021761595 : Real) / 2 ^ 40 <= Chebyshev.theta (8833512 : Real))
    (n : Nat) (h1 : 8833512 <= n) (h2 : n <= 11075303) :
    (((n : Real) + 1) - 2 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((12173656503993774110 : Real) / 2 ^ 40 <= Chebyshev.theta (11075304 : Real)) := by sorry
end TaoFivePrimes
