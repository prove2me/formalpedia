-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_auxiliary_nonlattice_coordinate_presentations
-- name    : WeierstrassEllipticZeta.auxiliary_nonlattice_coordinate_presentations
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T16:41:52.62857+00:00
-- url     : https://prove2.me/theorems/d94304b1-012c-4e19-bfb4-d6d014c2d097
-- title:
--   Quantitative rational coordinates on the nonlattice auxiliary grid
-- statement:
--   Let $L$ be a complex period pair with lattice $\Omega$, and let $\omega,u_1,u_2\in\mathbb C$ have regular auxiliary-grid data: integer grid points are distinct, their lattice congruences are determined by their first two coordinates, and every integer grid point shifted by $u_1/2$ is regular. The data include the grid cardinalities and shifted norm bounds, periodicity of $\wp,\wp'$, and the identity $\zeta(z+a\omega)=\zeta(z)+a\eta(\omega)$ at regular $z$ for every integer $a$.
--
--   Assume the canonical identity $\zeta'=-\wp$ off the lattice and the multiplied zeta and elliptic addition identities at regular arguments:
--
--   $$2(\wp(v)-\wp(z))\zeta(z+v)
--   =2(\zeta(z)+\zeta(v))(\wp(v)-\wp(z))+\wp'(v)-\wp'(z),$$
--
--   $$4(\wp(v)-\wp(z))^2\wp(z+v)
--   =-4(\wp(z)+\wp(v))(\wp(v)-\wp(z))^2+(\wp'(v)-\wp'(z))^2.$$
--
--   Let $\theta,\nu\in\mathbb C$, $g\in\mathbb Z[X,Y]$, and $d\in\mathbb Z[X]$, with $\delta=d(\theta)\ne0$. Assume every value in the following list has an integer bivariate polynomial presentation of $Y$-degree less than $\deg_Yg$ after multiplication by $\delta$:
--
--   $$g_2/4,g_3/4,\omega,\eta(\omega),u_1/2,u_2,
--   \zeta(u_1/2),\wp(u_1/2),\wp'(u_1/2),\wp''(u_1/2),$$
--
--   $$\wp(u_j),\wp'(u_j),\wp''(u_j),\zeta(u_j)\qquad(j=1,2).$$
--
--   Thus for each listed value $x$ there exists $P_x\in\mathbb Z[X,Y]$ such that $\deg_YP_x<\deg_Yg$ and $P_x(\theta,\nu)=\delta x$.
--
--   Then auxiliary nonlattice coordinate data hold:
--
--   $$\operatorname{AuxiliaryNonlatticeCoordinateData}(L,\omega,u_1,u_2,\theta,\nu).$$
--
--   Here is the full coordinate conclusion.
--
--   Fix a complex period pair with lattice $\Omega$, and complex numbers $\omega,u_1,u_2,\theta,\nu$. Write $z_0=u_1/2$ and let $\mathscr L(P)$ be the sum of the absolute values of the integer coefficients of a polynomial $P$. For a nonnegative integer $N$, put
--
--   $$s=\lfloor N^{3/16}\rfloor,\qquad q=\lfloor N^{5/8}\log N/64\rfloor,$$
--
--   $$\Gamma_3=\{a_1u_1+a_2u_2+a_3\omega: 0\le a_1,a_2<3s,\ 0\le a_3<3q,\ a_i\in\mathbb Z\}.$$
--
--   For a nonnegative integer $C$, use the coordinate degree and logarithmic length profiles
--
--   $$d_C=(C,Cs^2,Cs^2,Cs^2,C,C,C,C),$$
--
--   $$b_C=(C\log N,C(s^2+\log N),C(s^2+\log N),C(s^2+\log N),C,C,C,C).$$
--
--   A coordinate presentation at $v,z$ consists of eight numerator polynomials $P_a$, denominator polynomials $Q_a$ in $\mathbb Z[X,Y]$, and nonnegative integers $h_a$, such that
--
--   $$\deg P_a,\deg Q_a\le d_{C,a},\qquad
--   \mathscr L(P_a),\mathscr L(Q_a)\le h_a\le e^{b_{C,a}},$$
--
--   $$Q_a(\theta,\nu)\ne0,\qquad P_a(\theta,\nu)=Q_a(\theta,\nu)J_v(z)_a,$$
--
--   $$J_v(z)=(z+v,\zeta(v),\wp(v),\wp'(v),\zeta(z),\wp(z),\wp'(z),\wp''(z)).$$
--
--   Auxiliary nonlattice coordinate data assert
--
--   $$\exists C\in\mathbb N\ \forall N\text{ sufficiently large}\ \forall v\in\Gamma_3\setminus\Omega,
--   \quad\text{there exists a coordinate presentation at }v,z_0.$$
--
--   The constant and threshold precede all points. Every evaluated denominator is nonzero. The four fixed-coordinate bounds are independent of $N$, the ordinary coordinate has fixed degree and polynomial length in $N$, and the three moving elliptic coordinates have degree $O(s^2)$ and logarithmic length $O(s^2+\log N)$. No derivative matrices or analytic estimates are part of this coordinate property.
-- source:
--   Senthil Kumar K (2026), Section 5 Lemma 7(a), using the multiplication formulas and division-polynomial bounds of Section 4 Lemma 5, equation (12), and the fixed and ordinary coordinate bounds leading to (26)-(27). This is the coordinate-presentation form of that arithmetic step with nonzero denominators. The arbitrary constant absorbs the factor 3 in the enlarged side lengths; no unsupported exact degree constant is asserted. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_GridJetMatrices

open scoped Polynomial
open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.auxiliary_nonlattice_coordinate_presentations
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
    (θ ν : ℂ) (g : ℤ[X][X])
    (d : ℤ[X]) (hd : Polynomial.aeval θ d ≠ 0)
    (h_data : ∀ i : Fin 18, ∃ p : ℤ[X][X],
      p.natDegree < g.natDegree ∧
      p.eval₂ (Polynomial.aeval θ).toRingHom ν = Polynomial.aeval θ d *
        (![L.g₂/4, L.g₃/4, ω, zetaQuasiPeriod L ω, u₁/2, u₂,
        weierstrassZeta L (u₁/2), L.weierstrassP (u₁/2),
        L.derivWeierstrassP (u₁/2), deriv L.derivWeierstrassP (u₁/2),
        L.weierstrassP u₁, L.derivWeierstrassP u₁, deriv L.derivWeierstrassP u₁,
        weierstrassZeta L u₁, L.weierstrassP u₂, L.derivWeierstrassP u₂,
        deriv L.derivWeierstrassP u₂, weierstrassZeta L u₂] i)) :
    AuxiliaryNonlatticeCoordinateData L ω u₁ u₂ θ ν := by sorry
