-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_exists_complex_auxiliary_systems_from_arithmetic_jets
-- name    : WeierstrassEllipticZeta.exists_complex_auxiliary_systems_from_arithmetic_jets
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T11:57:41.732167+00:00
-- url     : https://prove2.me/theorems/fb05bd89-88f5-4afb-b7a6-3c8b0f4f0c28
-- title:
--   Auxiliary-system construction from arithmetic derivative presentations
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
--   Assume that $L$ has arithmetic jet data as follows.
--
--   For a period pair $L$, use the prescribed coordinate tuple
--
--   $$
--   J_v(z)=(z+v,\zeta(v),\wp(v),\wp'(v),\zeta(z),\wp(z),\wp'(z),\wp''(z))
--   $$
--
--   and the canonical cleared monomial
--
--   $$
--   G_v(z)=(z+v)^{l_0}[2(\wp(v)-\wp(z))]^{3M}
--   \wp(z+v)^{l_2}\zeta(z+v)^{l_3}.
--   $$
--
--   For nonnegative integers $l_0\le L_0$, $l_2,l_3\le M$, and $n$, set
--
--   $$
--   K=L_0+5M+n,\qquad k=(L_0,5M,5M,5M,K,K,K,K).
--   $$
--
--   Arithmetic jet data mean the following universal presentation property. Given eight pairs of integer bivariate polynomials $S_i,Q_i$, each pair having total degree at most $d_i$ and coefficient length at most $H_i$, there exists an integer bivariate polynomial $R$ with
--
--   $$
--   \deg R\le\sum_{i=0}^7 k_i d_i,
--   \qquad \ell(R)\le n!\,2^{41(L_0+M+n)}\prod_{i=0}^7 H_i^{k_i}.
--   $$
--
--   For every evaluation tuple $w\in\mathbb C^2$ and all $v,z,z+v$ outside the lattice, if
--
--   $$
--   S_i(w)=Q_i(w)J_v(z)_i\quad(0\le i<8),
--   $$
--
--   then
--
--   $$
--   R(w)=\left(\prod_{i=0}^7 Q_i(w)^{k_i}\right)G_v^{(n)}(z).
--   $$
--
--   The polynomial $R$ precedes the choices of $w,v,z$. The denominator product depends on $M,L_0,n$ and the $Q_i$, and is shared by all allowed monomial exponents. The fixed elliptic coordinates have exponents $5M$ independent of $L_0,n$. This is a multiplied polynomial identity; zero denominators are allowed, and no hypothesis on $\wp(v)-\wp(z)$ is imposed. Here coefficient length is the sum of absolute values of all integer coefficients.
--
--   Then there exist $a,c>0$ such that every sufficiently large $N$ admits a complex auxiliary system with
--
--   $$
--   b=(3+|\theta|+|\nu|)a,\qquad E<r.
--   $$
--
--   The system has the degree, height, size, and dimension-gap bounds in `ComplexAuxiliarySystem`. Every nonzero vector in its evaluated equation kernel with coordinate magnitudes at most $e^{bN}$ has a nonzero test value of magnitude at most $e^{-cN^2\log N}$. The matrices and finite test family precede the choice of vector.
--
--   The remaining construction must supply quantitative coordinate presentations on the auxiliary grids, reduce bivariate representatives modulo the monic polynomial $g$ with bounds, choose the asymptotic parameters, and prove interpolation and nonvanishing. The degree-controlled substitution of those coordinate presentations into the cleared derivatives is supplied by the arithmetic jet data. All original geometric, addition, and base arithmetic hypotheses are retained; the previous abstract derivative-polynomial and length hypotheses are replaced by this presentation property.
-- source:
--   Senthil Kumar K (2026), Section 5 Lemmas 7-10. This remaining auxiliary construction takes the quantitative substitution step of Lemma 7(b), equations (20)-(27), as arithmetic jet data. Division-polynomial grid presentations, bounded monic reduction, asymptotic estimates, interpolation and the zero estimate remain open. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_ArithmeticJets
import Definitions.Def_WeierstrassEllipticZeta_AuxiliaryGrids
import Definitions.Def_TranscendenceTheory_ComplexAuxiliarySystem
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Algebra.Polynomial.AlgebraMap

open scoped Polynomial
open Filter

open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.exists_complex_auxiliary_systems_from_arithmetic_jets
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
    (h_arithmetic : ArithmeticJetData L)
    (θ : ℂ) (hθ : Transcendental ℚ θ)
    (ν : ℂ)
    (g : ℤ[X][X]) (hg_monic : g.Monic) (hg_degree : 0 < g.natDegree)
    (hg_kernel : ∀ p : ℤ[X][X],
      p.eval₂ (Polynomial.aeval θ).toRingHom ν = 0 ↔ g ∣ p)
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
