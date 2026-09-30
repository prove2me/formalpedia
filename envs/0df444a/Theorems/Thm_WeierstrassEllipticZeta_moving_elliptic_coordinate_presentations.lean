-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_moving_elliptic_coordinate_presentations
-- name    : WeierstrassEllipticZeta.moving_elliptic_coordinate_presentations
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T17:19:24.996713+00:00
-- url     : https://prove2.me/theorems/9de98bb6-529e-429a-a322-47da5b5a871f
-- title:
--   Moving elliptic coordinate bounds from nine fixed generators
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
--   Let $\theta,\nu\in\mathbb C$ and $d\in\mathbb Z[X]$, with $\delta=d(\theta)\ne0$. Suppose each of the nine generator values
--
--   $$\eta_L(\omega),\quad g_2/4,\quad g_3/4,\quad
--   \wp_L(u_1),\quad\wp'_L(u_1),\quad\zeta_L(u_1),\quad
--   \wp_L(u_2),\quad\wp'_L(u_2),\quad\zeta_L(u_2)$$
--
--   has a polynomial $P_x\in\mathbb Z[X,Y]$ satisfying $P_x(\theta,\nu)=\delta x$.
--
--   Then moving elliptic coordinate data hold:
--
--   $$\operatorname{AuxiliaryMovingCoordinateData}(L,\omega,u_1,u_2,\theta,\nu).$$
--
--   The conclusion is specified fully below. No polynomial kernel or reduction-degree hypothesis is imposed on these generator presentations.
--
--   Fix a complex period pair $L$ with lattice $\Omega$, and complex numbers $\omega,u_1,u_2,\theta,\nu$. Let $\mathscr L(P)$ denote the sum of the absolute values of all integer coefficients of a polynomial. For sufficiently large positive integers $N$, put
--
--   $$s=\lfloor N^{3/16}\rfloor,\qquad q=\lfloor N^{5/8}\log N/64\rfloor,$$
--
--   $$\Gamma_3=\{a_1u_1+a_2u_2+a_3\omega:
--   0\le a_1,a_2<3s,\ 0\le a_3<3q,\ a_i\in\mathbb Z\}.$$
--
--   Moving elliptic coordinate data assert that there is a nonnegative integer $C$ such that, for every sufficiently large $N$ and every nonlattice point $v\in\Gamma_3$, there are three numerator polynomials $P_j$, denominator polynomials $Q_j$ in $\mathbb Z[X,Y]$, and nonnegative integers $h_j$, with
--
--   $$\deg P_j,\deg Q_j\le Cs^2,\qquad
--   \mathscr L(P_j),\mathscr L(Q_j)\le h_j\le e^{C(s^2+\log N)},$$
--
--   $$Q_j(\theta,\nu)\ne0,\qquad
--   P_j(\theta,\nu)=Q_j(\theta,\nu)y_j(v),\qquad
--   (y_0,y_1,y_2)=(\zeta_L,\wp_L,\wp'_L).$$
--
--   The constant and threshold precede all grid points. A presentation is the collection of these polynomials, bounds, and evaluation identities at one point. Numerators may vanish; evaluated denominators may not. This property concerns the three moving elliptic values only. The ordinary coordinate and the four fixed jet coordinates are supplied separately by the coordinate-completion theorem.
-- source:
--   Senthil Kumar K (2026), Section 5 Lemma 7(a), equation (19), using the multiplication formulas, torsion-zero property, and degree/height bounds in Section 4 Lemma 5, equation (12). The nine generator values are exactly the list in (19). Different coordinate denominators are allowed, and the constant absorbs the enlarged grid factor 3. The ordinary and fixed jet-coordinate construction is handled by the complete sibling theorem. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_MovingCoordinates

open scoped Polynomial
open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.moving_elliptic_coordinate_presentations
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
    (θ ν : ℂ) (d : ℤ[X]) (hd : Polynomial.aeval θ d ≠ 0)
    (h_generators : ∀ j : Fin 9, ∃ p : ℤ[X][X],
      p.eval₂ (Polynomial.aeval θ).toRingHom ν = Polynomial.aeval θ d *
        (![zetaQuasiPeriod L ω, L.g₂ / 4, L.g₃ / 4,
          L.weierstrassP u₁, L.derivWeierstrassP u₁, weierstrassZeta L u₁,
          L.weierstrassP u₂, L.derivWeierstrassP u₂, weierstrassZeta L u₂] j)) :
    AuxiliaryMovingCoordinateData L ω u₁ u₂ θ ν := by sorry
