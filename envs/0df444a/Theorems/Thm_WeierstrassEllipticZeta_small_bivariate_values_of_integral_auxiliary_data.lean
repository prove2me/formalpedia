-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_small_bivariate_values_of_integral_auxiliary_data
-- name    : WeierstrassEllipticZeta.small_bivariate_values_of_integral_auxiliary_data
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-05T11:22:26.898823+00:00
-- url     : https://prove2.me/theorems/7b4cc656-2e07-4c00-afa1-716cc44896b4
-- title:
--   Lemma 10: small values from a fixed integral model of the auxiliary data
-- statement:
--   Let $L$ be a complex period pair with lattice $\Omega$, and let $\omega\ne0$ belong to $\Omega$. Suppose $u_1,u_2,\omega$ are linearly independent over $\mathbb Q$ and $(\mathbb Zu_1+\mathbb Zu_2)\cap\Omega=\{0\}$. Assume the zeta derivative identity and the multiplied zeta and elliptic addition identities at all regular arguments.
--
--   Let $\theta$ be transcendental over $\mathbb Q$, and fix $\nu\in\mathbb C$ integral over $\mathbb Z[\theta]$. Suppose there is $d\in\mathbb Z[X]$ with $d(\theta)\ne0$ such that every entry $v_i$ of the eighteen-value list
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
--   admits a representation $d(\theta)v_i=p_i(\theta,\nu)$ with $p_i\in\mathbb Z[X,Y]$. Then there are constants $A,c>0$ such that every sufficiently large integer $N$ admits $P_N\in\mathbb Z[X,Y]$ satisfying
--
--   $$
--   \deg_XP_N,\deg_YP_N\le AN,\qquad
--   |[X^kY^j]P_N|\le e^{AN},\qquad
--   0<|P_N(\theta,\nu)|\le e^{-cN^2\log N}.
--   $$
--
--   The output uses the given fixed $\nu$. The constants may depend on the fixed model and the elliptic data. This is the auxiliary-function small-value construction after the integral field model has been supplied; the coefficient selection, interpolation, and nonvanishing estimates are part of the statement.
--
--   **Formalization Note.** The linear degree bounds relax the source's $O(N/\log N)$ bound in $X$ and fixed bound in $Y$. The original values need not be integral, and no Galois hypothesis is imposed.
-- source:
--   Senthil Kumar K (2026), Section 3 polynomial-denominator setup; Section 5 equation (18) and Lemmas 7–10, especially Lemma 10; https://doi.org/10.1017/S001309152610145X. Auxiliary construction in a fixed integral model containing all eighteen data. X-degree O(N/log N) and fixed Y-degree are relaxed to linear bounds. Integral-generator choice and algebraicity of the eighteen data are proved separately.

import Definitions.Def_WeierstrassEllipticZeta_Defs
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Algebra.Polynomial.AlgebraMap

open scoped Polynomial
open Filter

namespace WeierstrassEllipticZeta

theorem small_bivariate_values_of_integral_auxiliary_data
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
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
        ∀ᶠ N : ℕ in Filter.atTop, ∃ P : ℤ[X][X],
          (P.natDegree : ℝ) ≤ A * N ∧
          (∀ j, ((P.coeff j).natDegree : ℝ) ≤ A * N) ∧
          (∀ j k, |((P.coeff j).coeff k : ℝ)| ≤ Real.exp (A * N)) ∧
          P.eval₂ (Polynomial.aeval θ).toRingHom ν ≠ 0 ∧
          ‖P.eval₂ (Polynomial.aeval θ).toRingHom ν‖ ≤
            Real.exp (-c * (N : ℝ) ^ 2 * Real.log N) := by sorry

end WeierstrassEllipticZeta
