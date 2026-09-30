-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_small_integral_elements_of_algebraic_values
-- name    : WeierstrassEllipticZeta.small_integral_elements_of_algebraic_values
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-05T03:16:00.117099+00:00
-- url     : https://prove2.me/theorems/9ffd4fc5-7263-4808-a8e6-8ad434bab843
-- title:
--   Lemma 10: small integral elements from algebraic Weierstrass data
-- statement:
--   Let L be a complex period pair with lattice Ω, let ω≠0 belong to Ω, and let u₁,u₂,ω be linearly independent over Q, with (Zu₁+Zu₂)∩Ω={0}. Use the canonical Weierstrass functions and quasi-period η(ω) of this mission. Assume the zeta derivative identity and the multiplied zeta and elliptic addition identities at all regular arguments. Let θ be transcendental over Q, and suppose all ten values
--   $$
--   g_2,g_3,\omega,\eta(\omega),u_1,u_2,\wp(u_1),\zeta(u_1),\wp(u_2),\zeta(u_2)
--   $$
--   are algebraic over Q(θ).
--
--   There is a subring S of C containing θ, a finite basis b₀,…,b_d of S over Z[X] with X acting as θ and b₀=1, and constants C,c>0 such that every sufficiently large integer N admits x_N≠0 in S whose polynomial basis coordinates qᵢ(x_N) satisfy
--   $$
--   \deg q_i(x_N)\le CN,\qquad |[X^k]q_i(x_N)|\le e^{CN},\qquad
--   0<|x_N|\le e^{-cN^2\log N}.
--   $$
--   This is the integral-coordinate output of the auxiliary-function construction, before taking a field norm. It isolates Lemma 10 and its fixed algebraic setup from the subsequent norm-transfer argument. The ring and basis are independent of N. No integrality assertion is made for the original ten values.
--
--   **Formalization Note.** S is a subring of C and x_N≠0 is stated in S, so its complex modulus is positive. The algebraicity hypothesis is over Q[θ], equivalently its fraction field Q(θ). The linear degree bound is a relaxation of the source's O(N/log N) bound.
-- source:
--   Integral-coordinate consequence of Senthil Kumar K (2026), Section 3, first paragraphs and Lemma 1, and Section 5, equation (18), Lemmas 7–10, especially Lemma 10 and the first displayed coordinate expansion after it; https://doi.org/10.1017/S001309152610145X. Express Z[theta,nu] as a finite free Z[X]-algebra via X=theta and the integral power basis. Relax the coordinate degree O(N/log N) to O(N). This child includes the algebraic setup and auxiliary construction; it does not include the subsequent field norm.

import Definitions.Def_WeierstrassEllipticZeta_Defs
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.Polynomial.AlgebraMap

open scoped Polynomial
open Filter

namespace WeierstrassEllipticZeta

theorem small_integral_elements_of_algebraic_values
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
    ∃ (S : Subring ℂ) (hθS : θ ∈ S) (d : ℕ),
      letI : Algebra ℤ[X] S := (Polynomial.aeval (⟨θ, hθS⟩ : S)).toAlgebra
      ∃ b : Module.Basis (Fin (d + 1)) ℤ[X] S, b 0 = 1 ∧
        ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
          ∀ᶠ N : ℕ in Filter.atTop, ∃ x : S, x ≠ 0 ∧
            (∀ i, ((b.repr x i).natDegree : ℝ) ≤ C * N) ∧
            (∀ i k, |((b.repr x i).coeff k : ℝ)| ≤ Real.exp (C * N)) ∧
            ‖(x : ℂ)‖ ≤ Real.exp (-c * (N : ℝ) ^ 2 * Real.log N) := by sorry

end WeierstrassEllipticZeta
