-- Prove2me | Theorems.Thm_RobustRegLasso_Sparsity_theorem_6_some_solution
-- name    : RobustRegLasso.Sparsity.theorem_6_some_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:15:25.581311+00:00
-- url     : https://prove2.me/theorems/a55416b9-178f-4195-af0f-aff14cb5e317
-- title:
--   Theorem 6 (conclusion corrected: some optimal solution) — features nearly orthogonal to the relevant span get zero weight
-- statement:
--   Let $a_1,\dots,a_m, b \in \mathbb R^n$ and let all radii equal $c \ge 0$, so $\mathcal U = \{(\delta_1,\dots,\delta_m) \mid \|\delta_i\|_2 \le c\ \forall i\}$; the loss is $\ell^2$. Suppose there is $I \subseteq \{1,\dots,m\}$ such that for every $v \in \operatorname{span}(\{a_i,\ i\in I\}\cup\{b\})$ with $\|v\|_2 = 1$,
--   $$v^\top a_j \le c \qquad \text{for all } j \notin I.$$
--   Then the robust regression problem $\min_{x\in\mathbb R^m}\max_{\Delta A\in\mathcal U}\|b-(A+\Delta A)x\|_2$ has an optimal solution $x^*$ with $x^*_j = 0$ for all $j \notin I$.
--
--   This is the paper's incoherence-type sparsity criterion: a feature that is "nearly" (within an allowable perturbation) orthogonal to the response and to all relevant features receives zero weight.
--
--   **Formalization Note** The paper concludes "then **any** optimal solution $x^*$ satisfies $x^*_j = 0$ for all $j \notin I$". That is false: with $n = m = 2$, $c = 1$, $I = \{1\}$, $a_1 = e_2$, $a_2 = e_1$, $b = e_1$ the hypothesis holds, the objective is $\|(1-x_2, -x_1)\|_2 + |x_1| + |x_2| \ge 1$, and $x = (0, \tfrac12)$ attains $1$ with $x_2 \ne 0$. The paper's proof (via Theorem 5) establishes that **some** optimal solution is supported on $I$, which is what is stated here. The printed "$I \subset$" is read as $I \subseteq$. The hypothesis is kept in the printed form $v^\top a_j \le c$; since the span is closed under $v \mapsto -v$, it is equivalent to $|v^\top a_j| \le c$, which the proof uses. $c \ge 0$ is the standing convention for radii.
-- source:
--   Xu, Caramanis, Mannor, Robust Regression and Lasso, arXiv:0811.1790v1, p. 10, Theorem 6 (conclusion corrected)

import Mathlib
import Definitions.Def_RobustRegLasso_Sparsity_Basic

namespace RobustRegLasso.Sparsity

theorem theorem_6_some_solution {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (c : ℝ) (hc : 0 ≤ c) (I : Finset (Fin m))
    (hI : ∀ v ∈ Submodule.span ℝ ((a '' (I : Set (Fin m))) ∪ {b}), ‖v‖ = 1 →
      ∀ j, j ∉ I → inner ℝ v (a j) ≤ c) :
    ∃ xStar : Fin m → ℝ, IsRobustSolution a b (RobustRegLasso.FeatureWise.uncertaintySet (fun _ => c)) xStar ∧
      ∀ j, j ∉ I → xStar j = 0 := by sorry

end RobustRegLasso.Sparsity
