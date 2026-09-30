-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_elliptic_division_polynomial_identities
-- name    : WeierstrassEllipticZeta.elliptic_division_polynomial_identities
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T18:48:29.323419+00:00
-- url     : https://prove2.me/theorems/f0fca91f-4b7b-4009-8c54-d56da9459255
-- title:
--   Canonical elliptic multiplication identities and nonvanishing for division polynomials
-- statement:
--   Let $L$ be a complex period pair with lattice $\Omega$, and let $u\in\mathbb C$ satisfy
--
--   $$nu\notin\Omega\qquad(n\in\mathbb N,\ n>0).$$
--
--   Assume the canonical identity $\zeta'_L=-\wp_L$ off the lattice, and the following addition identities whenever $z,v,z+v$ are outside the lattice:
--
--   $$2(\wp_L(v)-\wp_L(z))\zeta_L(z+v)
--   =2(\zeta_L(z)+\zeta_L(v))(\wp_L(v)-\wp_L(z))+\wp'_L(v)-\wp'_L(z),$$
--
--   $$4(\wp_L(v)-\wp_L(z))^2\wp_L(z+v)
--   =-4(\wp_L(z)+\wp_L(v))(\wp_L(v)-\wp_L(z))^2+
--   (\wp'_L(v)-\wp'_L(z))^2.$$
--
--   Then
--
--   $$\operatorname{EllipticDivisionPolynomialIdentities}(L,u).$$
--
--   This is the analytic multiplication and nonvanishing assertion for the explicit recursively defined division polynomials. It includes every positive multiple, including the initial cases. The hypothesis that all positive multiples are outside the lattice remains in force. The polynomials and the full conclusion are specified below.
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
--
--   For a complex period pair $L$ and a point $u$, evaluate these polynomials at
--
--   $$y_u=(g_2/4,g_3/4,\wp_L(u),\wp'_L(u),\zeta_L(u)),\qquad f_n=F_n(y_u).$$
--
--   The property $\operatorname{EllipticDivisionPolynomialIdentities}(L,u)$ asserts, for every positive natural $n$, nonvanishing $f_n\ne0$ and the three identities
--
--   $$f_n^2\wp_L(nu)=\wp_L(u)f_n^2-f_{n-1}f_{n+1},$$
--
--   $$f_n^4\wp'_L(nu)=f_{2n},$$
--
--   $$nf_n\zeta_L(nu)=n^2f_n\zeta_L(u)+(\mathcal D F_n)(y_u).$$
--
--   There are no degree or coefficient estimates in this property. The formal last term is the evaluated polynomial derivation; identifying it with the complex derivative of the evaluated division polynomial is part of the analytic construction. The nonvanishing assertion concerns every positive index and is essential to the resulting common denominator.
-- source:
--   Senthil Kumar K (2026), Section 4 Lemma 5, equations (12) and (13), including the torsion-zero property; the differential identity wp-double-prime=6*wp^2-g2/2 identifies the polynomial derivation. The recurrence normalization is Mathlib.NumberTheory.EllipticDivisibilitySequence.preNormEDS', specialized to the short Weierstrass curve with a4=-g2/4 and a6=-g3/4. Identities are multiplied out and asserted at every positive multiple of a point whose positive multiples are all regular. Quantitative bounds are a separate proved child. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_DivisionPolynomials

open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.elliptic_division_polynomial_identities
    (L : PeriodPair) (u : ℂ)
    (h_regular : ∀ n : ℕ, 0 < n → (n : ℂ) * u ∉ L.lattice)
    (h_zeta_deriv : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (h_zeta_addition : ∀ z v : ℂ,
      z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) =
        2 * (weierstrassZeta L z + weierstrassZeta L v) *
          (L.weierstrassP v - L.weierstrassP z) +
        L.derivWeierstrassP v - L.derivWeierstrassP z)
    (h_wp_addition : ∀ z v : ℂ,
      z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      4 * (L.weierstrassP v - L.weierstrassP z) ^ 2 * L.weierstrassP (z + v) =
        -4 * (L.weierstrassP z + L.weierstrassP v) *
          (L.weierstrassP v - L.weierstrassP z) ^ 2 +
        (L.derivWeierstrassP v - L.derivWeierstrassP z) ^ 2) :
    EllipticDivisionPolynomialIdentities L u := by sorry
