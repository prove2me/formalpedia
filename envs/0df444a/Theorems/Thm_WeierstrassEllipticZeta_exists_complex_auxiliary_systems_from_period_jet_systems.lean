-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_exists_complex_auxiliary_systems_from_period_jet_systems
-- name    : WeierstrassEllipticZeta.exists_complex_auxiliary_systems_from_period_jet_systems
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T14:33:30.096571+00:00
-- url     : https://prove2.me/theorems/1b7cfb94-ca6d-4a58-85c9-5cd9c3499e1c
-- title:
--   Auxiliary-system construction with arithmetic derivative systems at period translates
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
--   Also assume the following elliptic regularization data.
--
--   Fix a period pair $L$ and complex numbers $\omega,u_1,u_2$. Write
--
--   $$\Phi_0=\zeta_L,\qquad\Phi_1=\wp_L,\qquad\Phi_2=\wp'_L.$$
--
--   Elliptic regularization data mean the following property. Supply entire functions $\sigma,S_0,S_1,S_2$ satisfying
--
--   $$S_j(z)=\sigma(z)^{j+1}\Phi_j(z)\qquad(z\notin L,\ 0\le j\le2).$$
--
--   For any finite index set $I$, complex shift $v$, complex coefficients $c_i$, and nonnegative integers $\ell_i,e_{ij},D,K$ with
--
--   $$\ell_i\le D,\qquad e_{i0}+2e_{i1}+3e_{i2}\le K,$$
--
--   put
--
--   $$f(z)=\sum_i c_i(z+v)^{\ell_i}\prod_{j=0}^2\Phi_j(z)^{e_{ij}}.$$
--
--   There is an entire function $G$, chosen independently of the radius, grid, and bounds, with $G=\sigma^Kf$ outside the lattice. If $B\ge1$ bounds the absolute values of $\sigma,S_0,S_1,S_2$ throughout $|z|\le R$, define
--
--   $$C_R=\left(\sum_i|c_i|\right)\max(1,R+|v|)^D B^K.$$
--
--   Then $|G(z)|\le C_R$ on $|z|\le R$. Moreover, choose nonnegative integers $A_1,A_2,A_3,T$ and radii $0<r<R$ such that
--
--   $$A_1|u_1|+A_2|u_2|+A_3|\omega|+|u_1|/2\le r.$$
--
--   Suppose all derivatives of $f$ below order $T$ vanish on
--
--   $$\{a_1u_1+a_2u_2+a_3\omega+u_1/2:0\le a_i<A_i\}.$$
--
--   Then, with $Q=TA_1A_2A_3$,
--
--   $$|G(z)|\le C_R(2r/R)^Q\qquad(|z|\le r),$$
--
--   $$|G^{(n)}(z)|\le \frac{n!}{\rho^n}C_R(2r/R)^Q
--   \qquad(\rho>0,\ |z|+\rho\le r,\ n\ge0).$$
--
--   The definition supplies the analytic extension and its interpolation consequences conditional on the four entire factors and their bounds. It does not assert existence of those factors or an order-two growth bound for them. At lattice points the entire extension need not equal the product formed from totalized meromorphic values.
--
--   Also assume cleared-addition entire data, as follows.
--
--   Let $L$ be a complex period pair, with lattice $\Omega$ and canonical functions $\zeta,\wp,\wp'$. Assume their multiplied addition identities at regular arguments. Supply entire functions $\sigma,S_0,S_1,S_2$ satisfying
--
--   $$S_0=\sigma\zeta,\qquad S_1=\sigma^2\wp,\qquad S_2=\sigma^3\wp'
--   \qquad\text{outside }\Omega.$$
--
--   Let $I$ be any finite index set, let $v\notin\Omega$, and choose complex coefficients $c_i$ and nonnegative integers $\ell_{0i},\ell_{2i},\ell_{3i},D,M$ with
--
--   $$\ell_{0i}\le D,\qquad\ell_{2i},\ell_{3i}\le M.$$
--
--   Define the translated, cleared auxiliary sum
--
--   $$f(z)=\sum_{i\in I}c_i(z+v)^{\ell_{0i}}
--   [2(\wp(v)-\wp(z))]^{3M}\wp(z+v)^{\ell_{2i}}\zeta(z+v)^{\ell_{3i}}.$$
--
--   There exists a single entire function $G$, chosen before any radius or bounds, with
--
--   $$G(z)=\sigma(z)^{15M}f(z)\qquad(z,z+v\notin\Omega).$$
--
--   Put
--
--   $$V_v=1+|\zeta(v)|+|\wp(v)|+|\wp'(v)|,\qquad K_v=36V_v^3.$$
--
--   For every $R\in\mathbb R$ and $B\ge1$, if all four basic entire functions are bounded in absolute value by $B$ on $|z|\le R$, then
--
--   $$|G(z)|\le C_R:=\left(\sum_i|c_i|\right)
--   \max(1,R+|v|)^D K_v^{15M}B^{90M}\qquad(|z|\le R).$$
--
--   The finite set may be empty, coefficients may vanish, and $D=M=0$ is allowed. Neither $\sigma$ nor the addition factor is assumed nonzero. The identity is restricted to regular arguments; the entire extension supplies its own values at poles. This is a conditional version of the construction in Lemma 6(ii), with a coarse explicit growth constant. It does not construct the basic sigma factors or assert the source's sharper displayed numerical bound.
--
--   For fixed $L,\omega,u_1,u_2$, cleared-addition entire data assert the preceding entire-extension and disk-bound property for every choice of the four basic factors, regular shift, finite coefficients, and exponents. The data also assert the following interpolation consequences for the same entire function $G$.
--
--   Let $A=(A_1,A_2,A_3)$ and $T$ be nonnegative integers. Suppose $0<r<R$, $B\ge1$, the four factors are bounded by $B$ on the closed radius-$R$ disk, and
--
--   $$A_1|u_1|+A_2|u_2|+A_3|\omega|+|u_1|/2\le r.$$
--
--   Write
--
--   $$\Gamma_A=\{a_1u_1+a_2u_2+a_3\omega+u_1/2:0\le a_i<A_i\}.$$
--
--   Assume $x+v\notin\Omega$ for every $x\in\Gamma_A$, and
--
--   $$f^{(t)}(x)=0\qquad(x\in\Gamma_A,\ 0\le t<T).$$
--
--   Then
--
--   $$|G(z)|\le C_R(2r/R)^{TA_1A_2A_3}\qquad(|z|\le r),$$
--
--   $$|G^{(n)}(z)|\le \frac{n!}{\rho^n}C_R(2r/R)^{TA_1A_2A_3}
--   \qquad(\rho>0,\ |z|+\rho\le r,\ n\ge0).$$
--
--   The entire function precedes all choices of grids, radii and bounds. The data do not provide the four basic factors, establish their nonvanishing or growth, or prove that a test value is nonzero.
--
--   Also assume the following period arithmetic jet-system data at $z=u_1/2$.
--
--   For fixed $L,\omega,z,\theta,\nu$, a monic relation $g\in\mathbb Z[X,Y]$, and $d\in\mathbb Z[X]$, the period arithmetic jet-system data assert the following uniform property. Write $\delta=d(\theta)$ and $e=\deg_Yg$. There exist positive integers $B,H$ such that for every integer $a$ and nonnegative integers $M,L_0,T$, with
--
--   $$I=\{0,\ldots,L_0\}\times\{0,\ldots,M\}^2,\qquad K_n=L_0+2M+n,$$
--
--   there is a matrix $R=(R_{n,i})_{0\le n<T,\,i\in I}$ over $\mathbb Z[X,Y]$ satisfying
--
--   $$\deg_YR_{n,i}<e,\qquad
--   \deg_X([Y^j]R_{n,i})\le BK_n\quad(j\ge0),$$
--
--   $$\mathscr L(R_{n,i})\le n!\,24^{K_n}(1+|a|)^{L_0+M}H^{K_n+1},$$
--
--   $$R_{n,i}(\theta,\nu)=\delta^{7K_n}
--   \left.\frac{d^n}{dw^n}\big(w^{i_0}\wp(w)^{i_2}\zeta(w)^{i_3}\big)
--   \right|_{w=z+a\omega}.$$
--
--   The same matrix, chosen before all coefficient vectors, satisfies for every $c\in\mathbb C^I$
--
--   $$\left[\sum_iR_{n,i}(\theta,\nu)c_i=0\ \ (0\le n<T)\right]
--   \iff
--   \left[\left.\frac{d^n}{dw^n}\sum_i c_iw^{i_0}\wp(w)^{i_2}\zeta(w)^{i_3}
--   \right|_{w=z+a\omega}=0\ \ (0\le n<T)\right].$$
--
--   The denominator exponent $7K_n$ is a uniform padding from coordinatewise clearing. It is explicitly coarser than the exponent in source equation (28); the degree and logarithmic height still have the required linear dependence on the degree and derivative parameters. The data concern only shifts by integer multiples of $\omega$. They neither supply coordinates at other grid points nor prove the zero estimate.
--
--   Then there exist $a,c>0$ such that every sufficiently large $N$ admits a complex auxiliary system with
--
--   $$
--   b=(3+|\theta|+|\nu|)a,\qquad E<r.
--   $$
--
--   The system has the degree, height, size, and dimension-gap bounds in `ComplexAuxiliarySystem`. Every nonzero vector in its evaluated equation kernel with coordinate magnitudes at most $e^{bN}$ has a nonzero test value of magnitude at most $e^{-cN^2\log N}$. The matrices and finite test family precede the choice of vector.
--
--   The new hypothesis supplies bounded reduced matrices and their exact derivative-kernel equivalence for every integer period shift. Quantitative coordinate presentations at nonlattice shifts, asymptotic parameter choices, construction and quadratic exponential growth of the basic sigma factors, and the zero estimate remain open. All previous hypotheses and the exact conclusion are retained.
-- source:
--   Senthil Kumar K (2026), Section 5 Lemmas 7-10, after supplying the period-translation arithmetic derivative systems corresponding to equation (28). Nonlattice coordinate arithmetic, parameters, basic sigma factors and their quadratic exponential bounds, and the zero estimate remain open. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_ReducedJetSystems
import Definitions.Def_WeierstrassEllipticZeta_GridInterpolation
import Definitions.Def_WeierstrassEllipticZeta_EntireRegularization
import Definitions.Def_WeierstrassEllipticZeta_ClearedEntire
import Definitions.Def_WeierstrassEllipticZeta_PeriodJets
import Definitions.Def_WeierstrassEllipticZeta_AuxiliaryGrids
import Definitions.Def_TranscendenceTheory_ComplexAuxiliarySystem
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Algebra.Polynomial.AlgebraMap

open scoped Polynomial
open Filter

open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.exists_complex_auxiliary_systems_from_period_jet_systems
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
    (h_regularization : EllipticRegularizationData L ω u₁ u₂)
    (h_cleared_entire : ClearedAdditionEntireData L ω u₁ u₂)
    (d : ℤ[X]) (hd : Polynomial.aeval θ d ≠ 0)
    (h_period_jets : PeriodArithmeticJetSystemData L ω (u₁ / 2) θ ν g d)
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
