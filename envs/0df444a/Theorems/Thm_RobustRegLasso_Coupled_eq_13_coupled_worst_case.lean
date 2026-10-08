-- Prove2me | Theorems.Thm_RobustRegLasso_Coupled_eq_13_coupled_worst_case
-- name    : RobustRegLasso.Coupled.eq_13_coupled_worst_case
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:18:45.069678+00:00
-- url     : https://prove2.me/theorems/b037df34-dd61-478b-bcbf-609a74605667
-- title:
--   Eq. (13) — the worst case over $\mathcal U'$ is $\|b-Ax\|_a + \sup_{c\in\mathcal Z} |x|^\top c$
-- statement:
--   Let $\|\cdot\|_a$ be an arbitrary norm on $\mathbb R^n$ with $n \ge 1$, let $a_1,\dots,a_m, b \in \mathbb R^n$, and let $f_1,\dots,f_k : \mathbb R^m \to \mathbb R$ be convex functions. Consider the coupled uncertainty set and the budget set
--   $$\mathcal U' = \{(\delta_1,\dots,\delta_m) : f_j(\|\delta_1\|_a,\dots,\|\delta_m\|_a) \le 0,\ j=1,\dots,k\},\qquad \mathcal Z = \{z \in \mathbb R^m : f_j(z) \le 0,\ j = 1,\dots,k;\ z \ge 0\}.$$
--   Then for every $x \in \mathbb R^m$,
--   $$\sup_{\Delta A \in \mathcal U'} \|b - (A+\Delta A)x\|_a = \|b - Ax\|_a + \sup_{c \in \mathcal Z} |x|^\top c,$$
--   where $|x| = (|x_1|,\dots,|x_m|)$ and both suprema are taken in the extended reals.
--
--   This identity reduces the robust problem over a coupled set to a convex maximization over the budgets $c$; Corollaries 1 and 2 evaluate its last term for specific sets $\mathcal Z$.
--
--   **Formalization Note.** The paper writes "max" on both sides; neither maximum need exist (e.g. $\mathcal Z$ empty or unbounded), so both are extended-real suprema: when $\mathcal Z = \emptyset$ both sides are $-\infty$, and when $|x|^\top c$ is unbounded on $\mathcal Z$ both sides are $+\infty$. The paper's first line, $\mathcal U' = \{(\delta_1,\dots,\delta_m) \mid c \in \mathcal Z;\ \|\delta_i\|_a \le c_i\}$, holds as a set identity only when $\mathcal Z$ is downward closed in $\mathbb R^m_+$; the identity (13) itself holds without that, and it is stated here for $\mathcal U'$ as defined on p. 6. The convexity of the $f_j$ is the paper's standing assumption and is not needed for (13). The norm space is nontrivial ($n \ge 1$).
-- source:
--   Xu, Caramanis, Mannor, Robust Regression and Lasso, arXiv:0811.1790v1, p. 19, Eq. (13), proof of Theorem 4, Appendix B; U′ and Z defined on p. 6

import Mathlib
import Definitions.Def_RobustRegLasso_Coupled_Basic

namespace RobustRegLasso.Coupled

/-- Eq. (13), proof of Theorem 4, Appendix B of arXiv:0811.1790v1, p. 19. For the coupled
uncertainty set `U′ = {(δ₁, …, δₘ) | f_j(‖δ₁‖ₐ, …, ‖δₘ‖ₐ) ≤ 0, j = 1, …, k}` with convex
`f_j : ℝᵐ → ℝ`, and `Z = {z ∈ ℝᵐ | f_j(z) ≤ 0, j = 1, …, k; z ≥ 0}`, for every `x`
`sup_{ΔA ∈ U′} ‖b − (A + ΔA)x‖ₐ = ‖b − Ax‖ₐ + sup_{c ∈ Z} |x|ᵀc`, both suprema taken in the extended
reals (so the identity also covers `Z = ∅`, both sides `⊥`, and an unbounded right-hand side, both
sides `⊤`). Requires `E ≠ 0` (`n ≥ 1`); the convexity of the `f_j` is the paper's standing
assumption. -/
theorem eq_13_coupled_worst_case {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] {m k : ℕ} (a : Fin m → E) (b : E) (f : Fin k → (Fin m → ℝ) → ℝ)
    (hf : ∀ j, ConvexOn ℝ Set.univ (f j)) (x : Fin m → ℝ) :
    robustObjective a b (coupledSet f) x =
      ((‖b - matVec a x‖ : ℝ) : EReal) +
        ⨆ c ∈ budgetSet f, ((∑ i, |x i| * c i : ℝ) : EReal) := by sorry

end RobustRegLasso.Coupled
