-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_compose_elliptic_generator_polynomials
-- name    : WeierstrassEllipticZeta.compose_elliptic_generator_polynomials
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T18:14:23.60105+00:00
-- url     : https://prove2.me/theorems/14fcc1e1-8fab-4a9b-b9c8-ff107b5b8f4c
-- title:
--   Combine elliptic multiplication polynomials by addition and period translation
-- statement:
--   Let $L$ be a complex period pair with lattice $\Omega$, and let $\omega,u_1,u_2$ have regular auxiliary-grid data. Thus the integer grid map is injective, an integer grid point belongs to the lattice precisely when its first two coordinates vanish, and two such points are congruent modulo the lattice precisely when their first two coordinates agree. Every integer grid point shifted by $u_1/2$ is outside the lattice. The data also give grid cardinalities, the shifted triangle-inequality radius bound, periodicity of $\wp_L,\wp'_L$, and
--
--   $$\zeta_L(z+a\omega)=\zeta_L(z)+a\eta_L(\omega)
--   \qquad(a\in\mathbb Z,\ z\notin\Omega).$$
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
--   Suppose that both points have single-point multiplication data:
--
--   $$\operatorname{EllipticMultiplePolynomialData}(L,u_1),\qquad
--   \operatorname{EllipticMultiplePolynomialData}(L,u_2).$$
--
--   Then
--
--   $$\operatorname{EllipticGeneratorPolynomialData}(L,\omega,u_1,u_2).$$
--
--   Thus the bounded common-denominator presentations for positive multiples of each point can be combined into bounded polynomials in the nine generators for every nonlattice natural grid point. The addition step treats both indices nonzero, and direct renaming handles either index zero. Period translation preserves the denominator, adds at most one to the degree, and adds only a factor linear in the period index to coefficient length. The full meanings of the two data properties follow.
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
--
--   Fix a complex period pair $L$, with lattice $\Omega$, and complex numbers $\omega,u_1,u_2$. The ordered generator tuple is
--
--   $$y=(\eta_L(\omega),g_2/4,g_3/4,\wp_L(u_1),\wp'_L(u_1),\zeta_L(u_1),
--   \wp_L(u_2),\wp'_L(u_2),\zeta_L(u_2)).$$
--
--   For a point $v$ and nonnegative integers $D,J$, a generator presentation consists of a common denominator $Q$ and three numerators $P_j$ in $\mathbb Z[Y_0,\ldots,Y_8]$, with total degrees at most $D$ and coefficient lengths at most $J$, satisfying
--
--   $$Q(y)\ne0,\qquad P_j(y)=Q(y)x_j(v),\qquad
--   (x_0,x_1,x_2)=(\zeta_L,\wp_L,\wp'_L).$$
--
--   Coefficient length means the sum of the absolute values of all integer coefficients. Numerators may vanish; the evaluated denominator may not.
--
--   The property $\operatorname{EllipticGeneratorPolynomialData}(L,\omega,u_1,u_2)$ asserts that there are positive integers $C,H$, chosen before all indices, with the following property. For every triple $a_1,a_2,a_3\in\mathbb N$, set
--
--   $$v=a_1u_1+a_2u_2+a_3\omega,\qquad T=a_1^2+a_2^2+1.$$
--
--   If $v\notin\Omega$, there is a generator presentation at $v$ with bounds
--
--   $$D=CT,\qquad J=(1+a_3)H^T.$$
--
--   Thus the degree is quadratic in the two nonperiodic indices and independent of the period index; the period index occurs only linearly in the coefficient-length bound. The constants may depend on the fixed lattice and generators. The polynomials may depend on the index triple. This property does not assert that one polynomial family works for every lattice. It contains no arithmetic parameters $\theta,\nu$, auxiliary integer $N$, or reduced polynomial model.
-- source:
--   Senthil Kumar K (2026), Section 5 Lemma 7(a), equation (19) and its proof, using addition identities (5), (6), and (11) and the single-point multiplication formulas (12). This theorem proves the addition and period-translation step from bounded single-point presentations, including nonzero denominators and zero-index boundary cases. The degree-four formulas, length bound 128, and composition constants 12 and 129 are explicit formalization choices; the denominator need not equal the particular factor in the paper. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_MultiplePolynomials

open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.compose_elliptic_generator_polynomials
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
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
        (L.derivWeierstrassP v - L.derivWeierstrassP z) ^ 2)
    (h₁ : EllipticMultiplePolynomialData L u₁)
    (h₂ : EllipticMultiplePolynomialData L u₂) :
    EllipticGeneratorPolynomialData L ω u₁ u₂ := by sorry
