-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_specialize_moving_elliptic_coordinates
-- name    : WeierstrassEllipticZeta.specialize_moving_elliptic_coordinates
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T17:39:49.676711+00:00
-- url     : https://prove2.me/theorems/43f1fac1-bd40-448d-ae2b-77f1a04c6dce
-- title:
--   Quantitative specialization of moving elliptic coordinates
-- statement:
--   Let $L$ be a complex period pair, let $\omega,u_1,u_2,\theta,\nu\in\mathbb C$, and let $d\in\mathbb Z[X]$ satisfy $\delta=d(\theta)\ne0$. Let $y$ be the nine-generator tuple specified below. Suppose that for each $y_j$ there is an integer bivariate polynomial $S_j$ such that
--
--   $$S_j(\theta,\nu)=\delta y_j.$$
--
--   Assume $\operatorname{EllipticGeneratorPolynomialData}(L,\omega,u_1,u_2)$, whose full meaning is given below. Then
--
--   $$\operatorname{AuxiliaryMovingCoordinateData}(L,\omega,u_1,u_2,\theta,\nu).$$
--
--   In particular, substitution and clearing the fixed denominator preserve a quadratic degree bound, an exponential coefficient-length bound with logarithmic period-index contribution, and nonzero evaluated denominators. A single natural constant and threshold work at every nonlattice point of the enlarged auxiliary grid. No transcendence, integrality, polynomial-kernel, reduced-degree, grid-independence, or derivative hypothesis is needed for this algebraic specialization step.
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
--   Supporting algebraic specialization of Senthil Kumar K (2026), Section 5 Lemma 7(a), equation (19), and the denominator-clearing argument in Lemma 7(b), equations (20)-(23). This theorem assumes the generator-polynomial estimates and proves their transfer to integer bivariate presentations. The factor 9 from coordinatewise clearing, the bound T <= 19*s^2 on the enlarged grid, and the N^4 period-index envelope are explicit formalization choices. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_GeneratorPolynomials

open scoped Polynomial
open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.specialize_moving_elliptic_coordinates
    (L : PeriodPair) (ω u₁ u₂ θ ν : ℂ)
    (d : ℤ[X]) (hd : Polynomial.aeval θ d ≠ 0)
    (h_generators : ∀ j : Fin 9, ∃ p : ℤ[X][X],
      p.eval₂ (Polynomial.aeval θ).toRingHom ν = Polynomial.aeval θ d *
        ellipticArithmeticGenerators L ω u₁ u₂ j)
    (h_polynomials : EllipticGeneratorPolynomialData L ω u₁ u₂) :
    AuxiliaryMovingCoordinateData L ω u₁ u₂ θ ν := by sorry
