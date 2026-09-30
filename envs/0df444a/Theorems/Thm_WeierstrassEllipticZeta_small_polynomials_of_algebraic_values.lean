-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_small_polynomials_of_algebraic_values
-- name    : WeierstrassEllipticZeta.small_polynomials_of_algebraic_values
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-05T00:25:12.466889+00:00
-- url     : https://prove2.me/theorems/ddd80eab-ff2b-4bd9-83cd-1bcc65375336
-- title:
--   Auxiliary integer polynomials from algebraic Weierstrass data
-- statement:
--   Let $L$ be a complex period pair with lattice $\Omega$, $\omega\ne0$ a lattice period, and $u_1,u_2,\omega$ linearly independent over $\mathbb Q$, with $(\mathbb Zu_1+\mathbb Zu_2)\cap\Omega=\{0\}$. Assume the canonical zeta derivative identity and the multiplied zeta and elliptic addition identities at regular points. Suppose all ten Theorem 1 values are algebraic over $\mathbb Q(\theta)$ for a transcendental complex number $\theta$. Then there are $A>0$ and $N_0\in\mathbb N$ such that every integer $N\ge N_0$ admits $P_N\in\mathbb Z[X]$ with
--
--   $$
--   \deg P_N\le AN,\qquad |[X^k]P_N|\le e^{AN}\quad(k\ge0),
--   \qquad 0<|P_N(\theta)|\le e^{-10(AN)^2}.
--   $$
--
--   This is a relaxed degree bound and strengthened eventual smallness threshold for the auxiliary construction followed by a field norm in Section 5. It isolates that construction from the polynomial transcendence criterion. The derivative and two addition identities are explicit input obligations. The fixed-base-point definition of the quasi-period remains the canonical mission definition.
--
--   **Formalization Note.** Algebraicity is over $\mathbb Q[\theta]$, equivalently its fraction field. The conclusion requires nonzero evaluated values, not merely nonzero polynomials.
-- source:
--   Derived consequence of Senthil Kumar K (2026), Section 5, Lemmas 7--10, and the final field-norm argument after Lemma 10, https://doi.org/10.1017/S001309152610145X. There the degree is O(N/log N), coefficient logarithms are O(N), and log absolute value is at most -c N^2 log N. Choose one positive linear envelope A and enlarge N0 until c log N >= 10 A^2. The algebraic data may lie in a finite extension of Q(theta); pass to a normal closure as in the source. This is an open construction lemma, not an assertion that the auxiliary-function argument has been formalized.

import Definitions.Def_WeierstrassEllipticZeta_Defs
import Mathlib.RingTheory.Algebraic.Defs

open scoped Polynomial

namespace WeierstrassEllipticZeta

/-- Linear-envelope consequence of the auxiliary construction and field-norm
step in Senthil Kumar (2026), Section 5, Lemmas 7--10 and its final paragraphs. -/
theorem small_polynomials_of_algebraic_values
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
    ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ p : ℤ[X],
        (p.natDegree : ℝ) ≤ A * N ∧
        (∀ k, |(p.coeff k : ℝ)| ≤ Real.exp (A * N)) ∧
        0 < ‖Polynomial.aeval θ p‖ ∧
        ‖Polynomial.aeval θ p‖ ≤ Real.exp (-10 * (A * N) ^ 2) := by sorry

end WeierstrassEllipticZeta
