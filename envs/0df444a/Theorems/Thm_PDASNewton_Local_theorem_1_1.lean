-- Prove2me | Theorems.Thm_PDASNewton_Local_theorem_1_1
-- name    : PDASNewton.Local.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:08:35.57803+00:00
-- url     : https://prove2.me/theorems/49007289-46fb-4878-97b6-95996ec5c23e
-- title:
--   Theorem 1.1, p. 3 — Newton's method with a slanting function with bounded inverses converges locally superlinearly
-- statement:
--   Let $X$ and $Z$ be real Banach spaces, $F : X \to Z$, and let $x^* \in X$ solve $F(x^*) = 0$. Suppose that $U$ is an open set containing $x^*$ and that $G : X \to \mathcal{L}(X, Z)$ is a slanting function for $F$ in $U$ (Definition 1). Suppose further that $G(x)$ is nonsingular for every $x \in U$, i.e. has a two-sided bounded linear inverse $G(x)^{-1}$, and that $\{\|G(x)^{-1}\| : x \in U\}$ is bounded.
--
--   Then there is $\rho > 0$ such that every Newton sequence
--   $$x^{k+1} = x^k - G(x^k)^{-1} F(x^k), \qquad k = 0, 1, 2, \dots$$
--   with $\|x^0 - x^*\| < \rho$ converges superlinearly to $x^*$.
--
--   This is the abstract local convergence theorem behind the paper; Theorem 3.1 is its application to the complementarity system (3.1).
--
--   **Formalization Note** The Newton step is written as its linear equation $G(x^k)(x^{k+1} - x^k) = -F(x^k)$, which is the same thing wherever $G(x^k)$ is invertible. The radius $\rho$ is chosen before the sequence and does not depend on it.
-- source:
--   Hintermüller, Ito, Kunisch, The primal-dual active set strategy as a semismooth Newton method, HAL hal-01660511v1, p. 3, Theorem 1.1 (cited from [CNQ])

import Mathlib
import Definitions.Def_PDASNewton_Local_Setting

namespace PDASNewton.Local

/-- Theorem 1.1, p. 3 ([CNQ]): if `x*` solves `F x = 0`, `F` is slantly differentiable on an open
neighbourhood `U` of `x*` with slanting function `G`, and `G x` is nonsingular for all `x ∈ U` with
`{‖G(x)⁻¹‖ : x ∈ U}` bounded, then the Newton iteration `x^{k+1} = x^k - G(x^k)⁻¹ F(x^k)` converges
superlinearly to `x*` whenever `‖x⁰ - x*‖` is sufficiently small. The iteration is written as its
linear equation `G(x^k)(x^{k+1} - x^k) = -F(x^k)`. -/
theorem theorem_1_1 {X Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    (F : X → Z) (G : X → X →L[ℝ] Z) (U : Set X) (xstar : X)
    (hU : IsOpen U) (hxU : xstar ∈ U) (hF : F xstar = 0)
    (hG : IsSlantingFunction F G U)
    (hinv : ∃ M : ℝ, ∀ x ∈ U, ∃ Ginv : Z →L[ℝ] X,
      Ginv.comp (G x) = ContinuousLinearMap.id ℝ X ∧
      (G x).comp Ginv = ContinuousLinearMap.id ℝ Z ∧ ‖Ginv‖ ≤ M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x : ℕ → X, ‖x 0 - xstar‖ < ρ →
      (∀ k, G (x k) (x (k + 1) - x k) = -F (x k)) → ConvergesSuperlinearly x xstar := by sorry

end PDASNewton.Local
