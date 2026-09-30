-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_exists_reduced_complex_auxiliary_systems
-- name    : WeierstrassEllipticZeta.exists_reduced_complex_auxiliary_systems
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T09:51:56.509164+00:00
-- url     : https://prove2.me/theorems/9fe629a9-0692-48dc-8251-a3f555c55508
-- title:
--   Reduced elliptic systems with bounded complex coefficients
-- statement:
--   Let $L$ be a complex period pair with lattice $\Omega$, let $0\ne\omega\in\Omega$, and suppose
--
--   $$
--   u_1,u_2,\omega\text{ are linearly independent over }\mathbb Q,
--   \qquad(\mathbb Zu_1+\mathbb Zu_2)\cap\Omega=\{0\}.
--   $$
--
--   Assume the canonical zeta derivative identity and the multiplied zeta and elliptic addition identities at regular arguments. Let $\theta$ be transcendental over $\mathbb Q$, and let $g\in\mathbb Z[X,Y]$ be monic of positive $Y$-degree $r$, with
--
--   $$
--   p(\theta,\nu)=0\quad\Longleftrightarrow\quad g\mid p.
--   $$
--
--   Let $d\in\mathbb Z[X]$ satisfy $d(\theta)\ne0$. Assume that multiplying each of the eighteen values
--
--   $$
--   g_2/4,g_3/4,\omega,\eta(\omega),u_1/2,u_2,
--   \zeta(u_1/2),\wp(u_1/2),\wp'(u_1/2),\wp''(u_1/2),
--   $$
--
--   $$
--   \wp(u_j),\wp'(u_j),\wp''(u_j),\zeta(u_j)\quad(j=1,2)
--   $$
--
--   by $d(\theta)$ gives an evaluation of an integer polynomial with $Y$-degree less than $r$. Then there are $a,c>0$ such that, for every sufficiently large $N$, a complex auxiliary system exists with
--
--   $$
--   b=(3+|\theta|+|\nu|)a,\qquad E<r.
--   $$
--
--   Its polynomial matrix entries have the degree, height, and size bounds of `ComplexAuxiliarySystem`. Every nonzero complex vector in the evaluated equation kernel with coordinates bounded by $e^{bN}$ has a nonzero test value of magnitude at most $e^{-cN^2\log N}$.
--
--   The system matrices and their finite test set are chosen before that coefficient vector. The remaining work comprises the cleared derivative presentations, grid estimates, interpolation and zero estimate. Reduced representatives and conversion of integer coefficient bounds to complex bounds are handled by separate lemmas.
-- source:
--   Senthil Kumar K (2026), Section 3 reduced representation before Lemma 1; Section 5 equation (18), Lemma 7 and equation (28), Lemma 8 equation (29), Lemma 6 analytic coefficient estimate, Lemma 9 zero estimate, and equations (34)-(35) and Lemma 10. Adapted to an explicit finite complex-vector interface, with fixed reduced Y-degree and relaxed linear X-degree bounds. The complex-vector property is the uniform analytic obligation, not an extra conclusion proved by defining the record. https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2

import Definitions.Def_WeierstrassEllipticZeta_Defs
import Definitions.Def_TranscendenceTheory_ComplexAuxiliarySystem
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Algebra.Polynomial.AlgebraMap

open scoped Polynomial
open Filter

namespace WeierstrassEllipticZeta

theorem exists_reduced_complex_auxiliary_systems
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (hω_ne : ω ≠ 0) (hω_period : ω ∈ L.lattice)
    (h_linearIndependent : LinearIndependent ℚ ![u₁, u₂, ω])
    (h_intersection : Submodule.span ℤ {u₁, u₂} ⊓ L.lattice = ⊥)
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

end WeierstrassEllipticZeta
