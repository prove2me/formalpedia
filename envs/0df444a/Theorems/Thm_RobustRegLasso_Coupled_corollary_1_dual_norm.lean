-- Prove2me | Theorems.Thm_RobustRegLasso_Coupled_corollary_1_dual_norm
-- name    : RobustRegLasso.Coupled.corollary_1_dual_norm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:18:50.815098+00:00
-- url     : https://prove2.me/theorems/f92e2114-bd6a-48df-9b01-69416b227d1d
-- title:
--   Corollary 1 — a norm budget $\|(\|\delta_i\|_a)_i\|_s \le l$ gives $\min_x \|b-Ax\|_a + l\|x\|_s^*$
-- statement:
--   Let $\|\cdot\|_a$ be an arbitrary norm on $\mathbb R^n$ with $n \ge 1$, let $a_1,\dots,a_m, b \in \mathbb R^n$ be the columns of $A$ and the response, let $\|\cdot\|_s$ be an absolute norm on $\mathbb R^m$ (that is, $\|(|z_1|,\dots,|z_m|)\|_s = \|z\|_s$ for every $z$), and let $l \ge 0$. Consider the uncertainty set
--   $$\mathcal U' = \big\{(\delta_1,\dots,\delta_m) : \big\|(\|\delta_1\|_a,\dots,\|\delta_m\|_a)\big\|_s \le l\big\}.$$
--   Then the robust regression problem $\min_x \max_{\Delta A \in \mathcal U'} \|b-(A+\Delta A)x\|_a$ is the regularized regression problem
--   $$\min_{x \in \mathbb R^m} \Big\{ \|b - Ax\|_a + l\,\|x\|_s^* \Big\},\qquad \|y\|_s^* = \sup_{\|z\|_s \le 1} y^\top z,$$
--   in the following sense:
--   1. for every $x$, the maximum of $\|b-(A+\Delta A)x\|_a$ over $\Delta A \in \mathcal U'$ is attained and equals $\|b-Ax\|_a + l\|x\|_s^*$;
--   2. a vector $x$ minimizes the robust objective if and only if it minimizes $\|b-Ax\|_a + l\|x\|_s^*$.
--
--   The corollary interprets an arbitrary norm-based regularizer as robustness to column disturbances whose norms are jointly bounded. The paper remarks that with both norms Euclidean, $\mathcal U'$ is a Frobenius-norm ball of matrices and the corollary reduces to the robust formulation of El Ghaoui and Lebret.
--
--   **Formalization Note.** The paper says "symmetric norm" without defining it; it is read as *absolute* (invariant under taking absolute values coordinatewise), which every symmetric gauge function is. Under the weaker reading "permutation invariant" the statement is false: on $\mathbb R^2$ take $\|z\|_s = \max(|z_1|,|z_2|) + |z_1+z_2|$, $l = 1$ and $x = (1,-1)$; then $\|x\|_s^* = 2$ but the worst-case excess is $2/3$. The paper does not state $l \ge 0$; for $l < 0$ the set $\mathcal U'$ is empty, so it is added. $n \ge 1$ is the nontriviality of the normed space $E$. The norm $\|\cdot\|_s$ is a Mathlib `Seminorm` with $N(z) = 0 \Rightarrow z = 0$, and $\|\cdot\|_s^*$ is the real supremum defined in the mission's definitions. "The resulting regularized regression problem is" is read, as in Theorem 3, as equal objectives with attained maximum at every $x$ and equal sets of minimizers.
-- source:
--   Xu, Caramanis, Mannor, Robust Regression and Lasso, arXiv:0811.1790v1, p. 7, Corollary 1

import Mathlib
import Definitions.Def_RobustRegLasso_Coupled_Basic

namespace RobustRegLasso.Coupled

/-- Corollary 1 of arXiv:0811.1790v1, p. 7. Let `‖·‖ₛ = N` be an absolute norm on `ℝᵐ` (the
paper's "symmetric norm"), `l ≥ 0`, and `U′ = {(δ₁, …, δₘ) | ‖(‖δ₁‖ₐ, …, ‖δₘ‖ₐ)‖ₛ ≤ l}`. Then
robust regression over `U′` is the regularized problem `min_x ‖b − Ax‖ₐ + l‖x‖*ₛ`: for every `x`
the worst-case residual over `U′` is attained and equals `‖b − Ax‖ₐ + l‖x‖*ₛ`, and the two problems
have the same minimizers. Requires `E ≠ 0` (`n ≥ 1`). -/
theorem corollary_1_dual_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] {m : ℕ} (a : Fin m → E) (b : E) (N : Seminorm ℝ (Fin m → ℝ))
    (hN : ∀ z, N z = 0 → z = 0) (hAbs : IsAbsolute N) (l : ℝ) (hl : 0 ≤ l) :
    (∀ x : Fin m → ℝ,
      IsGreatest (residualValues a b (normBudgetSet N l) x)
        (‖b - matVec a x‖ + l * dualNorm N x)) ∧
    {x : Fin m → ℝ | ∀ x' : Fin m → ℝ,
        robustObjective a b (normBudgetSet N l) x ≤ robustObjective a b (normBudgetSet N l) x'} =
      {x : Fin m → ℝ | ∀ x' : Fin m → ℝ,
        ‖b - matVec a x‖ + l * dualNorm N x ≤ ‖b - matVec a x'‖ + l * dualNorm N x'} := by sorry

end RobustRegLasso.Coupled
