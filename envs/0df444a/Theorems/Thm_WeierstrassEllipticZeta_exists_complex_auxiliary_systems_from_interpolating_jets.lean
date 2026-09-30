-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_exists_complex_auxiliary_systems_from_interpolating_jets
-- name    : WeierstrassEllipticZeta.exists_complex_auxiliary_systems_from_interpolating_jets
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T13:10:22.838705+00:00
-- url     : https://prove2.me/theorems/5ba6ee6e-ede7-4e08-b0bf-ef5be626d5a4
-- title:
--   Auxiliary-system construction with reduced jets and grid interpolation
-- statement:
--   Let $L$ be a complex period pair, and let $\omega,u_1,u_2\in\mathbb C$ have regular auxiliary-grid data. Thus integer grid points are distinct, their lattice congruences are determined by their first two coordinates, and every point shifted by $u_1/2$ is outside the lattice. The finite grids have cardinality $A_1A_2A_3$ and shifted radius at most
--
--   $$
--   A_1|u_1|+A_2|u_2|+A_3|\omega|+|u_1|/2.
--   $$
--
--   The data also include the elliptic periodicity formulas and
--
--   $$
--   \zeta(z+n\omega)=\zeta(z)+n\eta(\omega)
--   \qquad(n\in\mathbb Z,\ z\notin\Omega).
--   $$
--
--   Assume the canonical zeta derivative identity and the multiplied elliptic and zeta addition identities at regular arguments. Let $\theta$ be transcendental over $\mathbb Q$, let $\nu\in\mathbb C$, and let $g\in\mathbb Z[X,Y]$ be monic of positive $Y$-degree $r$ with
--
--   $$
--   p(\theta,\nu)=0\iff g\mid p.
--   $$
--
--   For a fixed $d\in\mathbb Z[X]$ with $d(\theta)\ne0$, assume the eighteen auxiliary values admit presentations of $Y$-degree less than $r$ after multiplication by $d(\theta)$. Those values are
--
--   $$
--   g_2/4,g_3/4,\omega,\eta(\omega),u_1/2,u_2,
--   \zeta(u_1/2),\wp(u_1/2),\wp'(u_1/2),\wp''(u_1/2),
--   $$
--
--   $$
--   \wp(u_j),\wp'(u_j),\wp''(u_j),\zeta(u_j)\quad(j=1,2).
--   $$
--
--   Assume reduced arithmetic jet-system data as follows.
--
--   Fix a period pair $L$, complex numbers $\theta,\nu$, and $g\in\mathbb Z[X][Y]$. For a polynomial, $\ell$ denotes the sum of the absolute values of all integer coefficients.
--
--   Reduced arithmetic jet-system data mean that there exist positive integers $B,H$ with the following property. For any nonnegative $M,L_0,T$, let
--
--   $$
--   I=\{0,\ldots,L_0\}\times\{0,\ldots,M\}^2,\qquad
--   k(n)=(L_0,5M,5M,5M,K_n,K_n,K_n,K_n),\quad K_n=L_0+5M+n.
--   $$
--
--   Choose eight numerator and denominator polynomials $S_a,Q_a\in\mathbb Z[X,Y]$, whose total degrees are at most $d_a$ and lengths at most $h_a$, respectively. There exists a matrix
--
--   $$
--   R=(R_{n,i})_{\substack{0\le n<T\\i\in I}}
--   $$
--
--   of integer bivariate polynomials. Writing $D_n=\sum_{a=0}^7 k_a(n)d_a$, every entry satisfies
--
--   $$
--   \deg_Y R_{n,i}<\deg_Yg,\qquad
--   \deg_X[Y^j]R_{n,i}\le BD_n\quad(j\ge0),
--   $$
--
--   $$
--   \ell(R_{n,i})\le
--   n!\,2^{41(L_0+M+n)}\left(\prod_{a=0}^7h_a^{k_a(n)}\right)H^{D_n+1}.
--   $$
--
--   This matrix precedes the following points and coefficient vectors. For any $v,z,z+v$ outside the lattice, suppose the coordinate presentations satisfy
--
--   $$
--   S_a(\theta,\nu)=Q_a(\theta,\nu)J_v(z)_a,
--   $$
--
--   where
--
--   $$
--   J_v(z)=(z+v,\zeta(v),\wp(v),\wp'(v),\zeta(z),\wp(z),\wp'(z),\wp''(z)).
--   $$
--
--   For $i=(i_0,i_2,i_3)$, set
--
--   $$
--   G_i(w)=(w+v)^{i_0}[2(\wp(v)-\wp(w))]^{3M}
--          \wp(w+v)^{i_2}\zeta(w+v)^{i_3},\qquad
--   \Delta_n=\prod_{a=0}^7Q_a(\theta,\nu)^{k_a(n)}.
--   $$
--
--   The exact entry evaluations are
--
--   $$
--   R_{n,i}(\theta,\nu)=\Delta_nG_i^{(n)}(z).
--   $$
--
--   If additionally $z-v$ is regular and all eight evaluated denominators are nonzero, then for every complex vector $c=(c_i)_{i\in I}$,
--
--   $$
--   \left(\forall\,0\le n<T,\ \sum_iR_{n,i}(\theta,\nu)c_i=0\right)
--   \ \Longleftrightarrow\
--   \left(\forall\,0\le n<T,\ F_c^{(n)}(z+v)=0\right),
--   $$
--
--   where
--
--   $$
--   F_c(w)=\sum_{i\in I}c_iw^{i_0}\wp(w)^{i_2}\zeta(w)^{i_3}.
--   $$
--
--   The exact evaluation identities also hold with zero coordinate denominators; nonzero denominators are required only for kernel equivalence. Constants are uniform in all cutoffs, orders, and presentations. The property assembles bounded reduced derivative presentations into finite linear equations. It does not produce grid-coordinate presentations, prove that their denominators are nonzero, choose asymptotic parameters, or establish a small nonzero test value.
--
--   Also assume auxiliary-grid interpolation data as follows.
--
--   Fix complex numbers $\omega,u_1,u_2$. For a triple of nonnegative integers $A=(A_1,A_2,A_3)$, let
--
--   $$
--   S_A=\{a_1u_1+a_2u_2+a_3\omega+u_1/2:
--              0\le a_i<A_i,\ a_i\in\mathbb Z\},
--   $$
--
--   $$
--   q_A=A_1|u_1|+A_2|u_2|+A_3|\omega|+|u_1|/2.
--   $$
--
--   Auxiliary-grid interpolation data mean the following property. Choose a nonnegative integer $T$, functions $f,G,\psi:\mathbb C\to\mathbb C$, with $G$ entire and $f,\psi$ analytic at every point of $S_A$. Suppose $G=\psi f$ in a neighborhood of each grid point and
--
--   $$
--   f^{(j)}(x)=0\qquad(x\in S_A,\ 0\le j<T).
--   $$
--
--   For all $0<r<R$ and $C\in\mathbb R$ with $q_A\le r$ and $|G(z)|\le C$ on $|z|=R$, put $N_A=TA_1A_2A_3$. Then
--
--   $$
--   |G(z)|\le C\left(\frac{2r}{R}\right)^{N_A}\qquad(|z|\le r),
--   $$
--
--   and, whenever $\rho>0$ and $|w|+\rho\le r$,
--
--   $$
--   |G^{(n)}(w)|\le\frac{n!}{\rho^n}\,C
--                      \left(\frac{2r}{R}\right)^{N_A}\qquad(n\ge0).
--   $$
--
--   The multiplier need not be nonzero. Empty grids and $T=0$ are included. This predicate records the effect of analytic regularization and interpolation once the regularized entire function and its outer-circle bound have been provided. It does not assert existence or growth estimates for a Weierstrass sigma regularizer.
--
--   Then there exist $a,c>0$ such that every sufficiently large $N$ admits a complex auxiliary system with
--
--   $$
--   b=(3+|\theta|+|\nu|)a,\qquad E<r.
--   $$
--
--   The system has the degree, height, size, and dimension-gap bounds in `ComplexAuxiliarySystem`. Every nonzero vector in its evaluated equation kernel with coordinate magnitudes at most $e^{bN}$ has a nonzero test value of magnitude at most $e^{-cN^2\log N}$. The matrices and finite test family precede the choice of vector.
--
--   Quantitative grid-coordinate presentations and their nonzero denominators, asymptotic parameter choices, construction and growth bounds of analytic regularizers, and the zero estimate remain open. The Schwarz and Cauchy estimates after analytic regularization are supplied by the interpolation hypothesis. The original arithmetic and grid hypotheses and the exact eventual auxiliary-system conclusion are retained.
-- source:
--   Senthil Kumar K (2026), Section 5 Lemmas 7-10, with the Schwarz and Cauchy estimates of Section 4 equations (14)-(15) supplied in their regularized grid form. Coordinate estimates, nonzero coordinate denominators, parameters, regularizer construction and growth, and the zero estimate remain explicit remaining work. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_ReducedJetSystems
import Definitions.Def_WeierstrassEllipticZeta_GridInterpolation
import Definitions.Def_WeierstrassEllipticZeta_AuxiliaryGrids
import Definitions.Def_TranscendenceTheory_ComplexAuxiliarySystem
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Algebra.Polynomial.AlgebraMap

open scoped Polynomial
open Filter

open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.exists_complex_auxiliary_systems_from_interpolating_jets
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
    (θ : ℂ) (hθ : Transcendental ℚ θ)
    (ν : ℂ)
    (g : ℤ[X][X]) (hg_monic : g.Monic) (hg_degree : 0 < g.natDegree)
    (hg_kernel : ∀ p : ℤ[X][X],
      p.eval₂ (Polynomial.aeval θ).toRingHom ν = 0 ↔ g ∣ p)
    (h_jet_systems : ReducedArithmeticJetSystemData L θ ν g)
    (h_interpolation : AuxiliaryGridInterpolationData ω u₁ u₂)
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
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        ∃ S : TranscendenceTheory.ComplexAuxiliarySystem
          θ ν a ((3 + ‖θ‖ + ‖ν‖) * a) c N,
          S.yDegree < g.natDegree := by sorry
