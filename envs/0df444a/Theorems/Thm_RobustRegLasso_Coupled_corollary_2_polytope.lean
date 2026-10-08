-- Prove2me | Theorems.Thm_RobustRegLasso_Coupled_corollary_2_polytope
-- name    : RobustRegLasso.Coupled.corollary_2_polytope
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:18:59.78353+00:00
-- url     : https://prove2.me/theorems/6cf74f5b-6d70-40ac-9532-8e04e0a386d0
-- title:
--   Corollary 2 — a polytope budget $\exists c\ge0: Tc\le s$ gives the linear program $\min \|b-Ax\|_a + s^\top\lambda$, $|x|\le T^\top\lambda$, $\lambda\ge0$
-- statement:
--   Let $\|\cdot\|_a$ be an arbitrary norm on $\mathbb R^n$ with $n \ge 1$, let $a_1,\dots,a_m, b \in \mathbb R^n$, $T \in \mathbb R^{k\times m}$ and $s \in \mathbb R^k$, and assume some $c \ge 0$ satisfies $Tc \le s$. Consider the polytope uncertainty set
--   $$\mathcal U' = \{(\delta_1,\dots,\delta_m) : \exists c \ge 0 : Tc \le s;\ \|\delta_j\|_a \le c_j\},$$
--   and for $x \in \mathbb R^m$ the set $D(x) = \{\lambda \in \mathbb R^k : x \le T^\top\lambda,\ -x \le T^\top\lambda,\ \lambda \ge 0\}$. Then the robust regression problem over $\mathcal U'$ is the problem
--   $$\text{minimize } \|b - Ax\|_a + s^\top\lambda \quad \text{subject to } x \le T^\top\lambda,\ -x \le T^\top\lambda,\ \lambda \ge 0,$$
--   in the following sense:
--   1. for every $x$, $\displaystyle\sup_{\Delta A\in\mathcal U'} \|b-(A+\Delta A)x\|_a = \|b-Ax\|_a + \inf_{\lambda \in D(x)} s^\top \lambda$ in the extended reals (both sides are $+\infty$ when $D(x)$ is empty);
--   2. for every $x$ with $D(x) \neq \emptyset$, the infimum over $D(x)$ is attained;
--   3. $x$ minimizes the robust objective if and only if there is $\lambda \in D(x)$ such that $(x,\lambda)$ is an optimal solution of the problem displayed above.
--
--   Polytope uncertainty sets lead to a final formulation that is linear apart from the loss term.
--
--   **Formalization Note.** The hypothesis that some $c \ge 0$ satisfies $Tc \le s$ is added: without it $\mathcal U'$ is empty and the robust objective is $-\infty$. Vector inequalities are coordinatewise. The suprema and infima are extended-real; "the resulting regularized regression problem is" is read as clauses 1–3. The norm space is nontrivial ($n \ge 1$).
-- source:
--   Xu, Caramanis, Mannor, Robust Regression and Lasso, arXiv:0811.1790v1, p. 7, Corollary 2

import Mathlib
import Definitions.Def_RobustRegLasso_Coupled_Basic

namespace RobustRegLasso.Coupled

/-- Corollary 2 of arXiv:0811.1790v1, p. 7. Let `T ∈ ℝ^{k×m}`, `s ∈ ℝᵏ`, and
`U′ = {(δ₁, …, δₘ) | ∃ c ≥ 0 : Tc ≤ s; ‖δⱼ‖ₐ ≤ cⱼ}`, and assume (added) that some `c ≥ 0` has
`Tc ≤ s`. Write `D(x) = {λ ∈ ℝᵏ | x ≤ Tᵀλ, −x ≤ Tᵀλ, λ ≥ 0}`. Then:
1. for every `x`, `sup_{ΔA ∈ U′} ‖b − (A + ΔA)x‖ₐ = ‖b − Ax‖ₐ + inf_{λ ∈ D(x)} sᵀλ` in the extended
   reals (both sides `⊤` when `D(x) = ∅`);
2. for every `x` with `D(x) ≠ ∅` the infimum is attained;
3. `x` minimizes the robust problem iff there is `λ ∈ D(x)` such that `(x, λ)` solves the linear
   program "minimize `‖b − Ax‖ₐ + sᵀλ` subject to `x ≤ Tᵀλ`, `−x ≤ Tᵀλ`, `λ ≥ 0`".
Requires `E ≠ 0` (`n ≥ 1`). -/
theorem corollary_2_polytope {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] {m k : ℕ} (a : Fin m → E) (b : E) (T : Matrix (Fin k) (Fin m) ℝ)
    (s : Fin k → ℝ)
    (hfeas : ∃ c : Fin m → ℝ, (∀ j, 0 ≤ c j) ∧ ∀ r, Matrix.mulVec T c r ≤ s r) :
    (∀ x : Fin m → ℝ,
      robustObjective a b (polytopeSet T s) x =
        ((‖b - matVec a x‖ : ℝ) : EReal) +
          ⨅ lam ∈ polytopeDualFeasible T x, ((∑ r, s r * lam r : ℝ) : EReal)) ∧
    (∀ x : Fin m → ℝ, (polytopeDualFeasible T x).Nonempty →
      ∃ lam ∈ polytopeDualFeasible T x, ∀ mu ∈ polytopeDualFeasible T x,
        ∑ r, s r * lam r ≤ ∑ r, s r * mu r) ∧
    (∀ x : Fin m → ℝ,
      (∀ x' : Fin m → ℝ,
        robustObjective a b (polytopeSet T s) x ≤ robustObjective a b (polytopeSet T s) x') ↔
      ∃ lam ∈ polytopeDualFeasible T x, ∀ x' : Fin m → ℝ, ∀ lam' ∈ polytopeDualFeasible T x',
        ‖b - matVec a x‖ + ∑ r, s r * lam r ≤ ‖b - matVec a x'‖ + ∑ r, s r * lam' r) := by sorry

end RobustRegLasso.Coupled
