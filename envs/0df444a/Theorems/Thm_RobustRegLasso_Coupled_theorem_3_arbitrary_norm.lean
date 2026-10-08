-- Prove2me | Theorems.Thm_RobustRegLasso_Coupled_theorem_3_arbitrary_norm
-- name    : RobustRegLasso.Coupled.theorem_3_arbitrary_norm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:18:41.746342+00:00
-- url     : https://prove2.me/theorems/fcf0f9fd-21ab-4a6e-88c9-080dcdd6f57d
-- title:
--   Theorem 3 — robust regression over $\mathcal U_a$ equals $\min_x \|b-Ax\|_a + \sum_i c_i|x_i|$ for an arbitrary norm
-- statement:
--   Let $\|\cdot\|_a$ be an arbitrary norm on $\mathbb R^n$ with $n \ge 1$, let $a_1,\dots,a_m, b \in \mathbb R^n$ be the columns of $A$ and the response, and let $c_1,\dots,c_m \ge 0$ be budgets. Consider the feature-wise uncertainty set
--   $$\mathcal U_a = \{(\delta_1,\dots,\delta_m) : \|\delta_i\|_a \le c_i,\ i=1,\dots,m\}.$$
--   Then the robust regression problem $\min_x \max_{\Delta A \in \mathcal U_a} \|b - (A+\Delta A)x\|_a$ is equivalent to the regularized regression problem
--   $$\min_{x \in \mathbb R^m} \Big\{ \|b - Ax\|_a + \sum_{i=1}^m c_i |x_i| \Big\}$$
--   in the following sense:
--   1. for every $x \in \mathbb R^m$, the maximum of $\|b-(A+\Delta A)x\|_a$ over $\Delta A \in \mathcal U_a$ is attained and equals $\|b-Ax\|_a + \sum_i c_i|x_i|$;
--   2. a vector $x$ minimizes the robust objective if and only if it minimizes the regularized objective.
--
--   This is Theorem 1 with the Euclidean norm replaced by an arbitrary norm; it is the step of the proof of (13) that evaluates the inner maximum for fixed budgets.
--
--   **Formalization Note.** $(\mathbb R^n, \|\cdot\|_a)$ is an arbitrary nontrivial real normed space $E$ (the nontriviality is the paper's implicit $n \ge 1$; with $n = 0$ the identity fails). The budgets $c_i \ge 0$ come from the setting of (2). "Is equivalent to" is read as: equal objectives at every $x$ (with the maximum attained) and equal sets of minimizers; existence of a minimizer is not claimed. The robust objective in the minimizer clause is the extended-real supremum.
-- source:
--   Xu, Caramanis, Mannor, Robust Regression and Lasso, arXiv:0811.1790v1, p. 6, Theorem 3

import Mathlib
import Definitions.Def_RobustRegLasso_Coupled_Basic

namespace RobustRegLasso.Coupled

/-- Theorem 3 of arXiv:0811.1790v1, p. 6. For an arbitrary norm `‖·‖ₐ` on `E` (with `E ≠ 0`, i.e.
`n ≥ 1`) and budgets `cᵢ ≥ 0`, the robust regression problem over
`Uₐ = {(δ₁, …, δₘ) | ‖δᵢ‖ₐ ≤ cᵢ}` is equivalent to the regularized problem
`min_x ‖b − Ax‖ₐ + ∑ᵢ cᵢ|xᵢ|`: for every `x` the worst-case residual is attained and equals
`‖b − Ax‖ₐ + ∑ᵢ cᵢ|xᵢ|`, and the two problems have the same minimizers. -/
theorem theorem_3_arbitrary_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] {m : ℕ} (a : Fin m → E) (b : E) (c : Fin m → ℝ) (hc : ∀ i, 0 ≤ c i) :
    (∀ x : Fin m → ℝ,
      IsGreatest (residualValues a b (uncertaintySetA c) x)
        (‖b - matVec a x‖ + ∑ i, c i * |x i|)) ∧
    {x : Fin m → ℝ | ∀ x' : Fin m → ℝ,
        robustObjective a b (uncertaintySetA c) x ≤ robustObjective a b (uncertaintySetA c) x'} =
      {x : Fin m → ℝ | ∀ x' : Fin m → ℝ,
        ‖b - matVec a x‖ + ∑ i, c i * |x i| ≤ ‖b - matVec a x'‖ + ∑ i, c i * |x' i|} := by sorry

end RobustRegLasso.Coupled
