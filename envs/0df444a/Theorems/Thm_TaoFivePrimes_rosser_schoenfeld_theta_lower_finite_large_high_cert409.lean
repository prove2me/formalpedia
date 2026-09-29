-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_high_cert409
-- name    : TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert409
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-27T19:01:28.482853+00:00
-- url     : https://prove2.me/theorems/7f901c63-d6ae-4884-9908-46b575112efc
-- title:
--   Rosser--Schoenfeld theta lower bound: high range, sieve shard 409
-- statement:
--   Let $\theta(x)=\sum_{p\le x}\log p$ be the Chebyshev theta function ($p$ prime, $\log$ natural) and suppose the integer $B$ below satisfies $B/2^{40}\le\theta(55355566)$.
--
--   Then for every integer $n$ with $55355566\le n\le57515675$,
--
--   $$
--   (n+1)-2\sqrt{n+1}\le\theta(n),
--   $$
--
--   and moreover the accumulated lower bound $A_{409}$ computed by the certificate satisfies $A_{409}/2^{40}\le\theta(57515676)$.
--
--   This is a sub-shard of the finite endpoint certificate of the high sub-range $10^6\le t\le10^8$ in Rosser and Schoenfeld's Theorem 19: the finite verification at the integer endpoints on which $\theta$ is constant. The certificate computes, for a chain of windows, the exact number of primes and the sum of their offsets above each window start (a bit-parallel sieve over the 1229 primes below $10^4$), converts $\log$ at the window start into a fixed-point lower bound, and checks at every checkpoint the exact integer inequality equivalent to $(x+1)-2\sqrt{x+1}\le\theta(x)$. The hypothesis is the quantitative carry handed on by the previous shard, so this shard starts from a tight lower bound for $\theta$; the second conjunct is the carry it hands to the next one.
--
--   **Formalization Note** The split is a Lean file with the whole sieve infrastructure inlined; the shards are independent (the previous carry enters as a hypothesis) and the leaf theorem chains them.
-- source:
--   J. B. Rosser and L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois Journal of Mathematics 6 (1962), Theorem 19, p. 82, eq. (4.6), https://doi.org/10.1215/ijm/1255631807 (finite integer endpoint certificate, high sub-range 10^6 <= n <= 10^8, sieve shard 409 of the refined split)

import Mathlib.NumberTheory.Chebyshev

namespace TaoFivePrimes
theorem rosser_schoenfeld_theta_lower_finite_large_high_cert409
    (hbase : (60853464886200808152 : Real) / 2 ^ 40 <= Chebyshev.theta (55355566 : Real))
    (n : Nat) (h1 : 55355566 <= n) (h2 : n <= 57515675) :
    (((n : Real) + 1) - 2 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((63231974305880872934 : Real) / 2 ^ 40 <= Chebyshev.theta (57515676 : Real)) := by sorry
end TaoFivePrimes
