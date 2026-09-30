-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_division_multiple_polynomial_bounds
-- name    : WeierstrassEllipticZeta.division_multiple_polynomial_bounds
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T18:48:32.335324+00:00
-- url     : https://prove2.me/theorems/769404bb-df0b-408e-8eb0-d57804d7c990
-- title:
--   Quadratic degree and exponential length bounds for elliptic multiplication polynomials
-- statement:
--   For the following explicit integer polynomials, there exist positive natural constants $C,J$, independent of the positive integer $n$, such that
--
--   $$\deg Q_n\le Cn^2,\quad L(Q_n)\le J^{n^2},$$
--
--   $$\deg P_{n,j}\le Cn^2,\quad L(P_{n,j})\le J^{n^2}\qquad(j=0,1,2).$$
--
--   Here $L(P)$ is the sum of the absolute values of all integer coefficients. The constants are universal for these formal polynomials; no lattice, evaluation point, nonvanishing, or analytic identity is assumed. In particular, this result also bounds each individual coefficient. The recurrences, derivation, and four polynomials are specified below.
--
--   Work in the integer polynomial ring in five independent variables, ordered as
--
--   $$(G,H,x,p,Z).$$
--
--   Set
--
--   $$\beta=16(x^3-Gx-H)^2,\qquad
--   \gamma=3x^4-6Gx^2-12Hx-G^2,$$
--
--   $$\delta=2x^6-10Gx^4-40Hx^3-10G^2x^2-8GHx+2G^3-16H^2.$$
--
--   Let $r_n=\operatorname{preNormEDS}'(\beta,\gamma,\delta,n)$ be Mathlib's auxiliary normalized elliptic-divisibility sequence. Explicitly, its initial terms and recurrences are
--
--   $$r_0=0,\quad r_1=r_2=1,\quad r_3=\gamma,\quad r_4=\delta,$$
--
--   $$r_{2k}=r_{k-1}^2r_kr_{k+2}-r_{k-2}r_kr_{k+1}^2\quad(k\ge3),$$
--
--   $$r_{2k+1}=r_{k+2}r_k^3\begin{cases}\beta&k\text{ even},\\1&k\text{ odd}\end{cases}
--   -r_{k-1}r_{k+1}^3\begin{cases}1&k\text{ even},\\\beta&k\text{ odd}\end{cases}\quad(k\ge2).$$
--
--   The reduced division polynomial is
--
--   $$F_n=r_n\begin{cases}p&n\text{ even},\\1&n\text{ odd}.\end{cases}$$
--
--   These are the usual division-polynomial representatives after using the cubic relation to replace even powers of $p$. The even factor is $p$, corresponding to $2y=\wp'$. The signs above correspond to the curve $y^2=x^3-Gx-H$.
--
--   Define the integer polynomial derivation $\mathcal D$ by
--
--   $$\mathcal D(G,H,x,p,Z)=(0,0,p,6x^2-2G,-x).$$
--
--   The explicit common denominator and three numerators are
--
--   $$Q_n=nF_n^4,$$
--
--   $$P_{n,0}=n^2F_n^4Z+F_n^3\mathcal D F_n,$$
--
--   $$P_{n,1}=n(xF_n^2-F_{n-1}F_{n+1})F_n^2,\qquad
--   P_{n,2}=nF_{2n}.$$
--
--   The definitions are total for natural indices; $n-1$ denotes truncated natural subtraction. Bounds and analytic multiplication claims below are required only for $n>0$.
-- source:
--   Senthil Kumar K (2026), Section 4 Lemma 5 and the division-polynomial estimates immediately preceding it, used in Section 5 Lemma 7(a). The explicit cleared numerators and denominator are obtained from equation (12). This theorem proves universal bounds for the recursively defined reduced polynomial representatives using Mathlib preNormEDS' and polynomial derivation estimates. Coefficient length replaces maximum coefficient height, and constants are enlarged. No analytic identities or nonvanishing are asserted. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_DivisionPolynomials

open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.division_multiple_polynomial_bounds : ∃ C H : ℕ, 0 < C ∧ 0 < H ∧
    ∀ n : ℕ, 0 < n →
      (ellipticDivisionDenominator n).totalDegree ≤ C * n ^ 2 ∧
      (∑ m ∈ (ellipticDivisionDenominator n).support,
        ((ellipticDivisionDenominator n).coeff m).natAbs) ≤ H ^ (n ^ 2) ∧
      (∀ j, (ellipticDivisionNumerator n j).totalDegree ≤ C * n ^ 2) ∧
      (∀ j, (∑ m ∈ (ellipticDivisionNumerator n j).support,
        ((ellipticDivisionNumerator n j).coeff m).natAbs) ≤ H ^ (n ^ 2)) := by sorry
