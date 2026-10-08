-- Prove2me | Theorems.Thm_PDASNewton_FunSpace_theorem_1_1
-- name    : PDASNewton.FunSpace.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:12:38.305131+00:00
-- url     : https://prove2.me/theorems/6d89bf06-26e7-4573-9349-89fdef00ba8f
-- title:
--   Theorem 1.1, p. 3 — slant differentiability near x* with uniformly bounded G(x)⁻¹ gives local superlinear convergence of the Newton iteration
-- statement:
--   Let $X$ and $Z$ be real Banach spaces, $F : X \to Z$, and $x^* \in X$ with $F(x^*) = 0$. Let $U$ be an open set containing $x^*$, and let $G : X \to \mathcal{L}(X, Z)$ be a slanting function for $F$ in $U$ (Definition 1). Suppose that $G(x)$ is invertible for every $x \in U$ and that $\{\|G(x)^{-1}\| : x \in U\}$ is bounded. Then there is $\rho > 0$ such that every sequence $(x_k)$ with $\|x_0 - x^*\| < \rho$ and
--   $$G(x_k)(x_{k+1} - x_k) = -F(x_k) \qquad (k \ge 0)$$
--   converges superlinearly to $x^*$.
--
--   This is the abstract local convergence theorem of semismooth Newton methods, which the paper attributes to Chen, Nashed and Qi; Theorem 4.1 applies it to the reduced map of §4.
--
--   **Formalization Note** The Newton iteration $x_{k+1} = x_k - G(x_k)^{-1}F(x_k)$ is written as its linear equation, which is the same thing wherever $G(x_k)$ is invertible. Invertibility is a two-sided continuous linear inverse with norm at most a common bound $M$.
-- source:
--   Hintermüller, Ito, Kunisch, The primal-dual active set strategy as a semismooth Newton method, HAL hal-01660511v1, p. 3, Theorem 1.1

import Mathlib
import Definitions.Def_PDASNewton_FunSpace_Setting

namespace PDASNewton.FunSpace

/-- Theorem 1.1, p. 3 ([CNQ]): if `F x* = 0`, `F` is slantly differentiable in an open
neighbourhood `U` of `x*` with slanting function `G`, and `G x` is invertible for every `x ∈ U`
with uniformly bounded inverses, then the Newton iteration `x_{k+1} = x_k - G(x_k)⁻¹ F(x_k)`
converges superlinearly to `x*` from every `x₀` close enough to `x*`. -/
theorem theorem_1_1 {X Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    (F : X → Z) (G : X → X →L[ℝ] Z) (U : Set X) (xstar : X)
    (hU : IsOpen U) (hxU : xstar ∈ U) (hF : F xstar = 0)
    (hslant : PDASNewton.Local.IsSlantingFunction F G U)
    (hinv : ∃ M : ℝ, ∀ x ∈ U, ∃ Ginv : Z →L[ℝ] X,
      Ginv.comp (G x) = ContinuousLinearMap.id ℝ X ∧
      (G x).comp Ginv = ContinuousLinearMap.id ℝ Z ∧ ‖Ginv‖ ≤ M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x : ℕ → X, ‖x 0 - xstar‖ < ρ →
      (∀ k, G (x k) (x (k + 1) - x k) = -F (x k)) →
      PDASNewton.Local.ConvergesSuperlinearly x xstar := by sorry

end PDASNewton.FunSpace
