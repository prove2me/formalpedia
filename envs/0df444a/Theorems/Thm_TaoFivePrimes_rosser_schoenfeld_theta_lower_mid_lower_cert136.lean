-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert136
-- name    : TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert136
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-08T11:26:19.823482+00:00
-- url     : https://prove2.me/theorems/e1c8ce3b-ccaf-4c1b-bf2f-0bf9a1f51f48
-- title:
--   Rosser--Schoenfeld (3.14) finite range $10^8\le t\le 10^9$: certificate segment 136 of 151
-- statement:
--   Let $\theta(x)=\sum_{p\le x}\log p$ be the Chebyshev theta function ($p$ prime, $\log$ natural), and suppose the integer $B=990885929667298500107$ satisfies $B/2^{40}\le\theta(901255308)$.
--
--   Then for every integer $n$ with $901255308\le n\le 907413293$,
--
--   $$
--   (n+1)-10\sqrt{n+1}\le\theta(n),
--   $$
--
--   and moreover the integer $A=997656295101403628344$ satisfies $A/2^{40}\le\theta(907413294)$.
--
--   Role: this is segment $136$ of $151$ consecutive segments covering $10^8\le n\le 10^9$, the finite verification behind the range $10^8<t\le10^9$ of Rosser and Schoenfeld's inequality (3.14), $t\,(1-1/(2\log t))<\theta(t)$ (Theorem 4), which is the parent node `TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_mid_lower`. Since $\theta$ is constant between consecutive integers, the bound at the integers $n$ with $n\le t<n+1$ gives the bound for real $t$, and $20\sqrt t<t/(2\log t)$ holds for $t\ge10^8$. The hypothesis is the lower bound for $\theta$ handed on by the previous segment (for the first segment it follows from `TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large` at $t=10^8$); the second conjunct is the lower bound this segment hands to the next one. Both conjuncts are unconditional finite statements about the primes up to $907413294$.
--
--   **Formalization Note** The constant $10$ in front of $\sqrt{n+1}$ is a formalization choice: it is weaker than the $2\sqrt{t}$ of Rosser--Schoenfeld's Theorem 19 (which is stated only up to $10^8$) and is all that (3.14) needs on this range. The segment endpoints and the integers $A$, $B$ are the exact values produced by the certificate chain; segment $k$'s $A$ is segment $k+1$'s $B$.
-- source:
--   J. B. Rosser and L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois Journal of Mathematics 6 (1962), 64--94, Theorem 4, p. 70, eq. (3.14), https://doi.org/10.1215/ijm/1255631807 (finite verification of the range 10^8 <= t <= 10^9, integer certificate segment 136 of 151; the finite part of the Five Primes node TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_mid_lower, used in T. Tao, arXiv:1201.6656, Section 9)

import Mathlib.NumberTheory.Chebyshev

namespace TaoFivePrimes

theorem rosser_schoenfeld_theta_lower_mid_lower_cert136
    (hbase : (990885929667298500107 : Real) / 2 ^ 40 <= Chebyshev.theta (901255308 : Real))
    (n : Nat) (h1 : 901255308 <= n) (h2 : n <= 907413293) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((997656295101403628344 : Real) / 2 ^ 40 <= Chebyshev.theta (907413294 : Real)) := by sorry

end TaoFivePrimes
