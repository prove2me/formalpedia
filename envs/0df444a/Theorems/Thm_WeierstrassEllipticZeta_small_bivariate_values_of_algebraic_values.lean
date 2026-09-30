-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_small_bivariate_values_of_algebraic_values
-- name    : WeierstrassEllipticZeta.small_bivariate_values_of_algebraic_values
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-05T04:04:04.122326+00:00
-- url     : https://prove2.me/theorems/0b14565f-1879-4cff-a3db-d99ca4f9be0d
-- title:
--   Lemma 10: small bivariate values at an integral generator
-- statement:
--   Let L be a complex period pair with lattice Ω, and use its canonical Weierstrass functions and the quasi-period η(ω) from this mission. Suppose ω≠0 belongs to Ω, u₁,u₂,ω are linearly independent over Q, and (Zu₁+Zu₂)∩Ω={0}. Assume the zeta derivative identity and the multiplied zeta and elliptic addition identities at all regular arguments. Let θ be transcendental over Q and suppose the ten values
--   $$
--   g_2,g_3,\omega,\eta(\omega),u_1,u_2,\wp(u_1),\zeta(u_1),\wp(u_2),\zeta(u_2)
--   $$
--   are algebraic over Q(θ).
--
--   There is a complex number ν integral over Z[θ] and constants A,c>0 such that every sufficiently large integer N admits P_N∈Z[X,Y] with
--   $$
--   \deg_X P_N,\deg_Y P_N\le AN,\qquad
--   |[X^kY^j]P_N|\le e^{AN},\qquad
--   0<|P_N(\theta,\nu)|\le e^{-cN^2\log N}.
--   $$
--   The generator ν and its monic integral relation are fixed independently of N. These are the small values furnished by the auxiliary-function construction before imposing a canonical power-basis normal form. No integrality assertion is made about the original ten values.
--
--   **Formalization Note.** Algebraicity is stated over Q[θ], equivalently over Q(θ). The two linear degree bounds are relaxations of the source's O(N/log N) bound in X and fixed bound in Y. The choice of an integral generator and the auxiliary-function, interpolation, and zero-estimate arguments remain part of this statement.
-- source:
--   Senthil Kumar K (2026), Section 3 integral-generator setup and displayed polynomial coordinate expansion preceding Lemma 1, and Section 5 equation (18), Lemmas 7–10, especially Lemma 10; https://doi.org/10.1017/S001309152610145X. Read the output xi_N as P_N(theta,nu), relaxing its X-degree O(N/log N) and fixed Y-degree to linear bounds. This statement retains the integral-generator choice and the auxiliary construction; quantitative reduction to a fixed basis is separated.

import Definitions.Def_WeierstrassEllipticZeta_Defs
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Algebra.Polynomial.AlgebraMap

open scoped Polynomial
open Filter

namespace WeierstrassEllipticZeta

theorem small_bivariate_values_of_algebraic_values
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
    (h_values : ∀ i, IsAlgebraic (Algebra.adjoin ℚ {θ})
      (theoremOneValues L ω u₁ u₂ i)) :
    ∃ ν : ℂ,
      (∃ f : ℤ[X][X], f.Monic ∧ f.eval₂ (Polynomial.aeval θ).toRingHom ν = 0) ∧
      ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
        ∀ᶠ N : ℕ in Filter.atTop, ∃ P : ℤ[X][X],
          (P.natDegree : ℝ) ≤ A * N ∧
          (∀ j, ((P.coeff j).natDegree : ℝ) ≤ A * N) ∧
          (∀ j k, |((P.coeff j).coeff k : ℝ)| ≤ Real.exp (A * N)) ∧
          P.eval₂ (Polynomial.aeval θ).toRingHom ν ≠ 0 ∧
          ‖P.eval₂ (Polynomial.aeval θ).toRingHom ν‖ ≤
            Real.exp (-c * (N : ℝ) ^ 2 * Real.log N) := by sorry

end WeierstrassEllipticZeta
