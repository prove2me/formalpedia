-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_elliptic_generator_polynomial_presentations
-- name    : WeierstrassEllipticZeta.elliptic_generator_polynomial_presentations
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T17:39:54.565721+00:00
-- url     : https://prove2.me/theorems/76b2420d-5034-451d-83bb-b997ee996c69
-- title:
--   Polynomial presentations in nine elliptic generators
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
--   Then the fixed generators have the following polynomial presentation property:
--
--   $$\operatorname{EllipticGeneratorPolynomialData}(L,\omega,u_1,u_2).$$
--
--   The constants are uniform over all natural index triples. The common denominator is required to evaluate to a nonzero number, including the cases in which one of the two nonperiodic indices vanishes. The exact property is specified below.
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
--   Senthil Kumar K (2026), Section 5 Lemma 7(a), equation (19), proved using Section 4 Lemma 5 and multiplication formulas (12), together with addition formulas (5), (6), and (11). This formulation retains a common nonzero denominator but does not prescribe its polynomial. It replaces the auxiliary-grid notation by arbitrary natural indices and records bounds C*(a1^2+a2^2+1), (1+a3)*H^(a1^2+a2^2+1). These follow the same division-polynomial degree and height estimates, with coefficient count absorbed into H and the zeta quasi-period term linear in a3. Construction of these polynomials is the remaining open analytic/algebraic task; arithmetic specialization is handled by the complete sibling. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_GeneratorPolynomials

open scoped Polynomial
open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.elliptic_generator_polynomial_presentations
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
        (L.derivWeierstrassP v - L.derivWeierstrassP z) ^ 2) :
    EllipticGeneratorPolynomialData L ω u₁ u₂ := by sorry
