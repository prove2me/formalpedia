-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_exists_complex_auxiliary_systems_from_reduced_arithmetic_jets
-- name    : WeierstrassEllipticZeta.exists_complex_auxiliary_systems_from_reduced_arithmetic_jets
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T12:26:24.894741+00:00
-- url     : https://prove2.me/theorems/e6a6f519-18cc-4931-af94-d50deace4e77
-- title:
--   Auxiliary-system construction from reduced arithmetic derivative presentations
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
--   Assume reduced arithmetic jet data as follows.
--
--   Fix a period pair $L$, complex numbers $\theta,\nu$, and an integer bivariate relation $g$. Write
--
--   $$
--   J_v(z)=(z+v,\zeta(v),\wp(v),\wp'(v),\zeta(z),\wp(z),\wp'(z),\wp''(z)),
--   $$
--
--   $$
--   G_v(z)=(z+v)^{l_0}[2(\wp(v)-\wp(z))]^{3M}\wp(z+v)^{l_2}\zeta(z+v)^{l_3}.
--   $$
--
--   Reduced arithmetic jet data mean that there exist positive integers $B,H$, uniform in all the following choices. For nonnegative integers $l_0\le L_0$, $l_2,l_3\le M$, and $n$, put
--
--   $$
--   K=L_0+5M+n,\qquad k=(L_0,5M,5M,5M,K,K,K,K).
--   $$
--
--   Given eight pairs of integer bivariate polynomials $S_i,Q_i$ with total degrees at most $d_i$ and coefficient lengths at most $h_i$, put
--
--   $$
--   D=\sum_{i=0}^7 k_i d_i,\qquad T=n!\,2^{41(L_0+M+n)}\prod_{i=0}^7 h_i^{k_i}.
--   $$
--
--   There exists $R\in\mathbb Z[X][Y]$ with
--
--   $$
--   \deg_Y R<\deg_Y g,\qquad \deg_X[Y^j]R\le BD\quad(j\ge0),\qquad \ell(R)\le T H^{D+1}.
--   $$
--
--   For every $v,z,z+v$ outside the lattice, if
--
--   $$
--   S_i(\theta,\nu)=Q_i(\theta,\nu)J_v(z)_i\quad(0\le i<8),
--   $$
--
--   then
--
--   $$
--   R(\theta,\nu)=\left(\prod_{i=0}^7Q_i(\theta,\nu)^{k_i}\right)G_v^{(n)}(z).
--   $$
--
--   Here $\ell$ sums the absolute values of all integer coefficients. The representative precedes the regular points $v,z$. Its $Y$-degree is bounded independently of the derivative order and monomial cutoffs. The denominator product is shared by all monomials under the same cutoffs. The identity allows zero coordinate denominators and imposes no nonvanishing condition on an elliptic-value difference. This property supplies reduced presentations once coordinate presentations are given; it does not itself provide those inputs or their nonvanishing.
--
--   Then there exist $a,c>0$ such that every sufficiently large $N$ admits a complex auxiliary system with
--
--   $$
--   b=(3+|\theta|+|\nu|)a,\qquad E<r.
--   $$
--
--   The system has the degree, height, size, and dimension-gap bounds in `ComplexAuxiliarySystem`. Every nonzero vector in its evaluated equation kernel with coordinate magnitudes at most $e^{bN}$ has a nonzero test value of magnitude at most $e^{-cN^2\log N}$. The matrices and finite test family precede the choice of vector.
--
--   The remaining construction must supply quantitative grid-coordinate presentations and nonzero denominators, choose asymptotic parameters, and establish interpolation and nonvanishing. Bounded reduction to the fixed power basis is supplied by the reduced arithmetic jet data. The geometric, addition, kernel, and eighteen base-presentation hypotheses and the eventual auxiliary-system conclusion are unchanged.
-- source:
--   Senthil Kumar K (2026), Section 5 Lemmas 7-10. This auxiliary construction assumes the quantitative monic reduction from Section 3 Lemma 1 has been applied to the arithmetic derivative presentations of Lemma 7(b). Quantitative grid presentations, nonzero denominators, parameters, interpolation and the zero estimate remain open. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_ReducedArithmeticJets
import Definitions.Def_WeierstrassEllipticZeta_AuxiliaryGrids
import Definitions.Def_TranscendenceTheory_ComplexAuxiliarySystem
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Algebra.Polynomial.AlgebraMap

open scoped Polynomial
open Filter

open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.exists_complex_auxiliary_systems_from_reduced_arithmetic_jets
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
    (h_reduced : ReducedArithmeticJetData L θ ν g)
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
