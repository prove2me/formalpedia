-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_exists_bounded_auxiliary_systems
-- name    : WeierstrassEllipticZeta.exists_bounded_auxiliary_systems
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T09:30:44.164958+00:00
-- url     : https://prove2.me/theorems/4c6554bc-3fd7-4bc9-99d7-3063c3dccb0b
-- title:
--   Elliptic auxiliary equations and interpolation test forms
-- statement:
--   Let $L$ be a complex period pair, with period lattice $\Omega$, and let $\omega\ne0$ belong to $\Omega$. Assume
--
--   $$
--   u_1,u_2,\omega\text{ are linearly independent over }\mathbb Q,
--   \qquad(\mathbb Zu_1+\mathbb Zu_2)\cap\Omega=\{0\}.
--   $$
--
--   Assume the canonical zeta derivative identity and the multiplied zeta and elliptic addition identities at regular arguments. Let $\theta$ be transcendental over $\mathbb Q$, let $\nu$ be integral over $\mathbb Z[\theta]$, and suppose a fixed polynomial $d\in\mathbb Z[X]$ satisfies $d(\theta)\ne0$ and clears all eighteen auxiliary values into $\mathbb Z[\theta,\nu]$. The values are
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
--   Then there are constants $a,c>0$ such that every sufficiently large integer $N$ admits a bounded bivariate system at $(\theta,\nu)$ in the sense of `TranscendenceTheory.BoundedBivariateSystem`.
--
--   Its polynomial matrix encodes the cleared vanishing equations of the auxiliary function; its test forms encode the candidate cleared derivative values on the enlarged grid. The system must have at least eight times as many polynomial unknowns as equations, and its degree, coefficient, and size bounds must be uniform with exponent $aN$. Every nonzero kernel vector of the prescribed degree and height must produce a nonzero test value of absolute value at most $e^{-cN^2\log N}$.
--
--   This is the remaining elliptic construction: arithmetic derivative presentations, grid estimates, interpolation, and the zero estimate are included. The finite Siegel coefficient-selection step is handled separately.
--
--   **Formalization Note.** All original geometric, analytic, and integral-model hypotheses are retained. The polynomial degree bounds are relaxed to linear bounds. The small-value requirement concerns evaluations; symbolic nonzero polynomials alone do not meet it.
-- source:
--   Senthil Kumar K (2026), Section 5, equation (18), Lemma 7 and equation (28) (cleared derivative entries), the linear system in the proof of Lemma 8 and equation (29), Lemma 9 (zero estimate), and equations (34)-(35) and Lemma 10 (small nonzero cleared test values). Adapted to the explicit BoundedBivariateSystem interface with rectangular degree bounds; Lemma 2 coefficient selection is separated. https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2

import Definitions.Def_WeierstrassEllipticZeta_Defs
import Definitions.Def_TranscendenceTheory_BoundedBivariateSystem
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Algebra.Polynomial.AlgebraMap

open scoped Polynomial
open Filter

namespace WeierstrassEllipticZeta

theorem exists_bounded_auxiliary_systems
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
    (hν : ∃ f : ℤ[X][X], f.Monic ∧ f.eval₂ (Polynomial.aeval θ).toRingHom ν = 0)
    (d : ℤ[X]) (hd : Polynomial.aeval θ d ≠ 0)
    (h_data : ∀ i : Fin 18, ∃ p : ℤ[X][X],
      p.eval₂ (Polynomial.aeval θ).toRingHom ν = Polynomial.aeval θ d *
        (![L.g₂/4, L.g₃/4, ω, zetaQuasiPeriod L ω, u₁/2, u₂,
        weierstrassZeta L (u₁/2), L.weierstrassP (u₁/2),
        L.derivWeierstrassP (u₁/2), deriv L.derivWeierstrassP (u₁/2),
        L.weierstrassP u₁, L.derivWeierstrassP u₁, deriv L.derivWeierstrassP u₁,
        weierstrassZeta L u₁, L.weierstrassP u₂, L.derivWeierstrassP u₂,
        deriv L.derivWeierstrassP u₂, weierstrassZeta L u₂] i)) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        Nonempty (TranscendenceTheory.BoundedBivariateSystem θ ν a c N) := by sorry

end WeierstrassEllipticZeta
