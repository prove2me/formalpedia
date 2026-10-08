-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert106
-- name    : TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert106
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-08T08:41:13.688989+00:00
-- url     : https://prove2.me/theorems/65a3d787-1f82-43e1-96ec-34cf8aca23c0
-- title:
--   Rosser--Schoenfeld (3.14) finite range $10^8\le t\le 10^9$: certificate segment 106 of 151
-- statement:
--   Let $\theta(x)=\sum_{p\le x}\log p$ be the Chebyshev theta function ($p$ prime, $\log$ natural), and suppose the integer $B=788890733729285756594$ satisfies $B/2^{40}\le\theta(717526298)$.
--
--   Then for every integer $n$ with $717526298\le n\le 723611423$,
--
--   $$
--   (n+1)-10\sqrt{n+1}\le\theta(n),
--   $$
--
--   and moreover the integer $A=795586522840378970913$ satisfies $A/2^{40}\le\theta(723611424)$.
--
--   Role: this is segment $106$ of $151$ consecutive segments covering $10^8\le n\le 10^9$, the finite verification behind the range $10^8<t\le10^9$ of Rosser and Schoenfeld's inequality (3.14), $t\,(1-1/(2\log t))<\theta(t)$ (Theorem 4), which is the parent node `TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_mid_lower`. Since $\theta$ is constant between consecutive integers, the bound at the integers $n$ with $n\le t<n+1$ gives the bound for real $t$, and $20\sqrt t<t/(2\log t)$ holds for $t\ge10^8$. The hypothesis is the lower bound for $\theta$ handed on by the previous segment (for the first segment it follows from `TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large` at $t=10^8$); the second conjunct is the lower bound this segment hands to the next one. Both conjuncts are unconditional finite statements about the primes up to $723611424$.
--
--   **Formalization Note** The constant $10$ in front of $\sqrt{n+1}$ is a formalization choice: it is weaker than the $2\sqrt{t}$ of Rosser--Schoenfeld's Theorem 19 (which is stated only up to $10^8$) and is all that (3.14) needs on this range. The segment endpoints and the integers $A$, $B$ are the exact values produced by the certificate chain; segment $k$'s $A$ is segment $k+1$'s $B$.
-- source:
--   J. B. Rosser and L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois Journal of Mathematics 6 (1962), 64--94, Theorem 4, p. 70, eq. (3.14), https://doi.org/10.1215/ijm/1255631807 (finite verification of the range 10^8 <= t <= 10^9, integer certificate segment 106 of 151; the finite part of the Five Primes node TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_mid_lower, used in T. Tao, arXiv:1201.6656, Section 9)

import Mathlib.NumberTheory.Chebyshev

namespace TaoFivePrimes

theorem rosser_schoenfeld_theta_lower_mid_lower_cert106
    (hbase : (788890733729285756594 : Real) / 2 ^ 40 <= Chebyshev.theta (717526298 : Real))
    (n : Nat) (h1 : 717526298 <= n) (h2 : n <= 723611423) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((795586522840378970913 : Real) / 2 ^ 40 <= Chebyshev.theta (723611424 : Real)) := by sorry

end TaoFivePrimes
