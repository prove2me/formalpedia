-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_high_cert412
-- name    : TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert412
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-27T19:01:40.77368+00:00
-- url     : https://prove2.me/theorems/e7e98570-9b0c-4c7d-83ea-416d67584e51
-- title:
--   Rosser--Schoenfeld theta lower bound: high range, sieve shard 412
-- statement:
--   Let $\theta(x)=\sum_{p\le x}\log p$ be the Chebyshev theta function ($p$ prime, $\log$ natural) and suppose the integer $B$ below satisfies $B/2^{40}\le\theta(61913430)$.
--
--   Then for every integer $n$ with $61913430\le n\le63889722$,
--
--   $$
--   (n+1)-2\sqrt{n+1}\le\theta(n),
--   $$
--
--   and moreover the accumulated lower bound $A_{412}$ computed by the certificate satisfies $A_{412}/2^{40}\le\theta(63889723)$.
--
--   This is a sub-shard of the finite endpoint certificate of the high sub-range $10^6\le t\le10^8$ in Rosser and Schoenfeld's Theorem 19: the finite verification at the integer endpoints on which $\theta$ is constant. The certificate computes, for a chain of windows, the exact number of primes and the sum of their offsets above each window start (a bit-parallel sieve over the 1229 primes below $10^4$), converts $\log$ at the window start into a fixed-point lower bound, and checks at every checkpoint the exact integer inequality equivalent to $(x+1)-2\sqrt{x+1}\le\theta(x)$. The hypothesis is the quantitative carry handed on by the previous shard, so this shard starts from a tight lower bound for $\theta$; the second conjunct is the carry it hands to the next one.
--
--   **Formalization Note** The split is a Lean file with the whole sieve infrastructure inlined; the shards are independent (the previous carry enters as a hypothesis) and the leaf theorem chains them.
-- source:
--   J. B. Rosser and L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois Journal of Mathematics 6 (1962), Theorem 19, p. 82, eq. (4.6), https://doi.org/10.1215/ijm/1255631807 (finite integer endpoint certificate, high sub-range 10^6 <= n <= 10^8, sieve shard 412 of the refined split)

import Mathlib.NumberTheory.Chebyshev

namespace TaoFivePrimes
theorem rosser_schoenfeld_theta_lower_finite_large_high_cert412
    (hbase : (68062654158748796066 : Real) / 2 ^ 40 <= Chebyshev.theta (61913430 : Real))
    (n : Nat) (h1 : 61913430 <= n) (h2 : n <= 63889722) :
    (((n : Real) + 1) - 2 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((70238451534093005511 : Real) / 2 ^ 40 <= Chebyshev.theta (63889723 : Real)) := by sorry
end TaoFivePrimes
