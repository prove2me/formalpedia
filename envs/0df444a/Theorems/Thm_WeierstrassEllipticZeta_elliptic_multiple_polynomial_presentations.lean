-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_elliptic_multiple_polynomial_presentations
-- name    : WeierstrassEllipticZeta.elliptic_multiple_polynomial_presentations
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T18:14:27.940082+00:00
-- url     : https://prove2.me/theorems/a278dd9a-e501-4595-aecd-ef5c17952044
-- title:
--   Bounded polynomial presentations at positive multiples of one elliptic point
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
--   $$\operatorname{EllipticMultiplePolynomialData}(L,u).$$
--
--   This means that the three canonical elliptic values at every positive multiple admit a common nonzero polynomial denominator in the five fixed generators, with degree quadratic and coefficient length exponential in the square of the index. The full property is specified below. This is the remaining single-point division-polynomial construction; no two-point grid or arithmetic specialization is part of the conclusion.
--
--   Fix a complex period pair $L$ with lattice $\Omega$ and a point $u\in\mathbb C$. The five single-point generators are
--
--   $$y_u=(g_2/4,g_3/4,\wp_L(u),\wp'_L(u),\zeta_L(u)).$$
--
--   For natural numbers $n,D,J$, a multiple presentation consists of a common denominator $Q$ and three numerators $P_j$ in $\mathbb Z[Y_0,\ldots,Y_4]$. All four polynomials have total degree at most $D$ and coefficient length at most $J$, where coefficient length is the sum of the absolute values of the integer coefficients. They satisfy
--
--   $$Q(y_u)\ne0,\qquad P_j(y_u)=Q(y_u)x_j(nu),\qquad
--   (x_0,x_1,x_2)=(\zeta_L,\wp_L,\wp'_L).$$
--
--   The property $\operatorname{EllipticMultiplePolynomialData}(L,u)$ asserts that there are positive natural constants $C,H$, chosen before all indices, such that for every positive integer $n$ there is a multiple presentation with
--
--   $$D=Cn^2,\qquad J=H^{n^2}.$$
--
--   Numerators may vanish. Evaluated denominators may not. There is no requirement at index zero. The constants and polynomials may depend on the fixed lattice and point; the polynomials may also depend on the index. The predicate itself asserts these presentations at all positive indices. The theorem establishing it assumes that all positive multiples of the point are outside the lattice. No arithmetic parameters, auxiliary grid, or period generator occur in this property.
-- source:
--   Senthil Kumar K (2026), Section 4 Lemma 5 and equation (12), together with wp-double-prime=6*wp^2-g2/2, as used in the one-index-zero cases of Section 5 Lemma 7(a). A possible common denominator is n*f_n(u)^4. The formulas give integer polynomial numerators in g2/4,g3/4,wp(u),wp-prime(u),zeta(u); the torsion-zero property and the hypothesis on all positive multiples ensure nonvanishing. Degree and height estimates give C*n^2 and H^(n^2), with coefficient count and powers of n absorbed into H. Index zero is excluded. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_MultiplePolynomials

open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.elliptic_multiple_polynomial_presentations
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
    EllipticMultiplePolynomialData L u := by sorry
