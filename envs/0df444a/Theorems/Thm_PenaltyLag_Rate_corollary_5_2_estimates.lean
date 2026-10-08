-- Prove2me | Theorems.Thm_PenaltyLag_Rate_corollary_5_2_estimates
-- name    : PenaltyLag.Rate.corollary_5_2_estimates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:45:00.971895+00:00
-- url     : https://prove2.me/theorems/44f9580e-40e3-446a-a745-01cd730e9bba
-- title:
--   Corollary 5.2, (5.15)–(5.17) — a|xᵏ − ξ(yᵏ)|² ≤ αₖ, |ξ(yᵏ) − x̄| ≍ |yᵏ − ȳ|_I, g_r(ȳ) − g_r(yᵏ) ≍ |yᵏ − ȳ|²
-- statement:
--   In the setting of Corollary 5.2 (the standing assumptions of §5, $r > 0$, a bounded maximizing sequence $\{y^k\}$ for $(D_r)$, points $x^k \in X$ satisfying (4.7) with $\alpha_k \to 0$), let $\xi(y)$ be a minimizer of $L_r(\cdot, y)$ over $X$ whenever one exists (by Theorem 5.1 (iv) it is unique near $\bar y$). Write $|y|_I^2 = \sum_{i \in I} y_i^2$ with $I = \{i : f_i(\bar x) = 0\}$. Then there exist positive constants $a, b_1, b_2, c_1, c_2$ such that for all sufficiently large $k$
--   $$
--   a |x^k - \xi(y^k)|^2 \le \alpha_k, \qquad (5.15)
--   $$
--   $$
--   b_1 |y^k - \bar y|_I \le |\xi(y^k) - \bar x| \le b_2 |y^k - \bar y|_I, \qquad (5.16)
--   $$
--   $$
--   c_1 |y^k - \bar y|^2 \le g_r(\bar y) - g_r(y^k) \le c_2 |y^k - \bar y|^2. \qquad (5.17)
--   $$
--
--   These estimates translate the accuracy of the inner minimization ($\alpha_k$) and of the dual iterate ($y^k$) into distances to the primal and dual optima.
--
--   **Formalization Note** "With $\xi(y)$ as defined in Theorem 5.1" is encoded by a function $\xi$ that picks a minimizer of $L_r(\cdot, y)$ over $X$ whenever one exists; eventually $y^k$ lies where the minimizer is unique, so $\xi(y^k)$ is the paper's. The differences $g_r(\bar y) - g_r(y^k)$ are in `EReal` (finite eventually). $|\cdot|_I$ is `normOn (activeSet f x̄)`. The hypothesis of Theorem 4.1 that the asymptotic optimal value is finite is omitted as automatic.
-- source:
--   Rockafellar, A Dual Approach to Solving Nonlinear Programming Problems by Unconstrained Optimization, Math. Programming 5 (1973), pp. 370–371, Corollary 5.2, (5.15)–(5.17)

import Mathlib
import Definitions.Def_PenaltyLag_Rate_Basic

open Filter Topology

namespace PenaltyLag.Rate

/-- Corollary 5.2, (5.15)–(5.17), pp. 370–371: in the setting of Corollary 5.2, with ξ(y) a
minimizer of L_r(·, y) over X whenever one exists (the ξ of Theorem 5.1), there are positive
constants a, b₁, b₂, c₁, c₂ such that for all sufficiently large k
a|xᵏ − ξ(yᵏ)|² ≤ αₖ, b₁|yᵏ − ȳ|_I ≤ |ξ(yᵏ) − x̄| ≤ b₂|yᵏ − ȳ|_I, and
c₁|yᵏ − ȳ|² ≤ g_r(ȳ) − g_r(yᵏ) ≤ c₂|yᵏ − ȳ|². -/
theorem corollary_5_2_estimates
    {n m : ℕ} (X : Set (Pt n)) (hX : Convex ℝ X)
    (f₀ : Pt n → ℝ) (f : Fin m → Pt n → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (xbar : Pt n) (ybar : Mult m) (hA : Sec5Assumptions X f₀ f xbar ybar)
    (r : ℝ) (hr : 0 < r)
    (y : ℕ → Mult m) (hyb : Bornology.IsBounded (Set.range y)) (hymax : IsMaximizing X f₀ f r y)
    (x : ℕ → Pt n) (hxX : ∀ k, x k ∈ X)
    (α : ℕ → ℝ) (hα : Tendsto α atTop (𝓝 0))
    (h47 : ∀ k, (Lr f₀ f r (x k) (y k) : EReal) - gr X f₀ f r (y k) ≤ (α k : EReal))
    (ξ : Mult m → Pt n)
    (hξ : ∀ y' : Mult m, (∃ x' ∈ X, ∀ x'' ∈ X, Lr f₀ f r x' y' ≤ Lr f₀ f r x'' y') →
      ξ y' ∈ X ∧ ∀ x'' ∈ X, Lr f₀ f r (ξ y') y' ≤ Lr f₀ f r x'' y') :
    ∃ a b₁ b₂ c₁ c₂ : ℝ, 0 < a ∧ 0 < b₁ ∧ 0 < b₂ ∧ 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ k in atTop,
      a * ‖x k - ξ (y k)‖ ^ 2 ≤ α k ∧
      b₁ * normOn (activeSet f xbar) (y k - ybar) ≤ ‖ξ (y k) - xbar‖ ∧
      ‖ξ (y k) - xbar‖ ≤ b₂ * normOn (activeSet f xbar) (y k - ybar) ∧
      ((c₁ * ‖y k - ybar‖ ^ 2 : ℝ) : EReal) ≤ gr X f₀ f r ybar - gr X f₀ f r (y k) ∧
      gr X f₀ f r ybar - gr X f₀ f r (y k) ≤ ((c₂ * ‖y k - ybar‖ ^ 2 : ℝ) : EReal) := by sorry

end PenaltyLag.Rate
