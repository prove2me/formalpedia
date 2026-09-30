-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_complete_auxiliary_nonlattice_coordinates
-- name    : WeierstrassEllipticZeta.complete_auxiliary_nonlattice_coordinates
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T17:19:25.152717+00:00
-- url     : https://prove2.me/theorems/3873d649-229b-4caa-aca7-7602fac592a1
-- title:
--   Complete all jet coordinates from the three moving elliptic values
-- statement:
--   Let $L$ be a complex period pair, let $\omega,u_1,u_2,\theta,\nu\in\mathbb C$, and put $z_0=u_1/2$. Let $d\in\mathbb Z[X]$ satisfy $\delta=d(\theta)\ne0$. Suppose the seven fixed values
--
--   $$z_0,\quad u_2,\quad\omega,\quad\zeta_L(z_0),\quad
--   \wp_L(z_0),\quad\wp'_L(z_0),\quad\wp''_L(z_0)$$
--
--   admit integer bivariate polynomial presentations after multiplication by $\delta$. Precisely, for each listed value $x_j$, there is $P_j\in\mathbb Z[X,Y]$ with
--
--   $$P_j(\theta,\nu)=\delta x_j.$$
--
--   Assume moving elliptic coordinate data on the enlarged grid, as specified below. Then all eight nonlattice jet coordinates have quantitative presentations:
--
--   $$\operatorname{AuxiliaryNonlatticeCoordinateData}(L,\omega,u_1,u_2,\theta,\nu).$$
--
--   The full profiles distinguish the ordinary coordinate, the three moving elliptic coordinates, and the four fixed coordinates. The conclusion requires one common constant and threshold, and nonzero evaluated denominators in every coordinate. No transcendence assumption, polynomial kernel, monicity assumption, grid independence, or addition identity is needed for this completion step. The complete moving-coordinate hypothesis and eight-coordinate conclusion follow.
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
--   Supporting coordinate-level formulation of Senthil Kumar K (2026), Section 5, equations (26)-(27) in the proof of Lemma 7(b), using the moving presentations from Lemma 7(a). The theorem constructs the ordinary and four fixed coordinates, assuming only seven fixed polynomial presentations and the three moving-coordinate bounds. The exponent 4 in the local ordinary-length estimate is an explicit formalization choice, not a source constant. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_MovingCoordinates

open scoped Polynomial
open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.complete_auxiliary_nonlattice_coordinates
    (L : PeriodPair) (ω u₁ u₂ θ ν : ℂ)
    (d : ℤ[X]) (hd : Polynomial.aeval θ d ≠ 0)
    (h_fixed : ∀ j : Fin 7, ∃ p : ℤ[X][X],
      p.eval₂ (Polynomial.aeval θ).toRingHom ν = Polynomial.aeval θ d *
        (![u₁ / 2, u₂, ω, weierstrassZeta L (u₁ / 2), L.weierstrassP (u₁ / 2),
          L.derivWeierstrassP (u₁ / 2), deriv L.derivWeierstrassP (u₁ / 2)] j))
    (h_moving : AuxiliaryMovingCoordinateData L ω u₁ u₂ θ ν) :
    AuxiliaryNonlatticeCoordinateData L ω u₁ u₂ θ ν := by sorry
