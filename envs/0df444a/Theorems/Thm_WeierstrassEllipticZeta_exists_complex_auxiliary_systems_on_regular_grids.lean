-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_exists_complex_auxiliary_systems_on_regular_grids
-- name    : WeierstrassEllipticZeta.exists_complex_auxiliary_systems_on_regular_grids
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T10:14:31.12657+00:00
-- url     : https://prove2.me/theorems/d5b905a8-3033-46de-80e8-39e0492253ff
-- title:
--   Elliptic auxiliary systems on explicit regular finite grids
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
--   Then there exist $a,c>0$ such that every sufficiently large $N$ admits a complex auxiliary system with
--
--   $$
--   b=(3+|\theta|+|\nu|)a,\qquad E<r.
--   $$
--
--   The system has the degree, height, size, and dimension-gap bounds in `ComplexAuxiliarySystem`. Every nonzero vector in its evaluated equation kernel with coordinate magnitudes at most $e^{bN}$ has a nonzero test value of magnitude at most $e^{-cN^2\log N}$. The matrices and finite test family precede the choice of vector.
--
--   This isolates the remaining derivative presentations, parameter estimates, interpolation, and zero estimate after the grid geometry, counts, radius, and integer-period translations have been supplied. It does not assume those remaining analytic conclusions.
-- source:
--   Senthil Kumar K (2026), Section 5 Gamma definition before Lemma 7, Lemmas 7-9 and equations (28)-(35), Lemma 10; Section 4 Lemmas 4 and 6; Appendix (A.10). The existing reduced complex-system interface is retained, while the original geometric hypotheses are replaced by their explicit grid consequences. No original arithmetic or analytic hypothesis is changed. https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2

import Definitions.Def_WeierstrassEllipticZeta_AuxiliaryGrids
import Definitions.Def_TranscendenceTheory_ComplexAuxiliarySystem
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Algebra.Polynomial.AlgebraMap

open scoped Polynomial
open Filter

open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.exists_complex_auxiliary_systems_on_regular_grids
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
