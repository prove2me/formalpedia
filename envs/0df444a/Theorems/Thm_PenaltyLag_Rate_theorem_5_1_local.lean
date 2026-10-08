-- Prove2me | Theorems.Thm_PenaltyLag_Rate_theorem_5_1_local
-- name    : PenaltyLag.Rate.theorem_5_1_local
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:44:48.375081+00:00
-- url     : https://prove2.me/theorems/ba3fb1b3-bc4f-46af-83c5-5b528fc4a6e2
-- title:
--   Theorem 5.1 (i)–(iii) — near the optimum, x ∈ int X, L_r is C² and given by (5.4), and ∇²ₓL_r(x, y) is positive definite
-- statement:
--   Assume the standing assumptions of §5 for $(\bar x, \bar y)$, with $X \subset \mathbb R^n$ convex and $f_0, \dots, f_m$ convex on $X$, and let $I = \{i : f_i(\bar x) = 0\}$. For arbitrary $r > 0$ and $\beta > 0$ there exist $\varepsilon > 0$ and $\alpha > 0$ such that for all $y \in \mathbb R^m$ and $x \in X$ satisfying
--   $$
--   \sup g_r - g_r(y) \le \varepsilon \quad (5.2), \qquad L_r(x, y) - \inf_{X} L_r(\cdot, y) \le \alpha \quad (5.3),
--   $$
--   the following hold:
--
--   1. $|y - \bar y| \le \beta$, $|x - \bar x| \le \beta$ and $x \in \operatorname{int} X$;
--   2. $L_r$ is twice continuously differentiable with respect to $(x, y)$ at $(x, y)$, and on a neighborhood of $(x, y)$
--   $$
--   L_r(x', y') = f_0(x') + \sum_{i \in I} \big[y'_i f_i(x') + r f_i(x')^2\big] - \frac{1}{4r} \sum_{i \notin I} y_i'^2 ; \qquad (5.4)
--   $$
--   3. the Hessian $\nabla^2_x L_r(x, y)$ is positive definite: $z \cdot \nabla_x^2 L_r(x, y) z > 0$ for every $z \neq 0$.
--
--   The order of quantifiers is essential: $\varepsilon$ and $\alpha$ are chosen after $r$ and $\beta$, and work for every pair $(x, y)$ satisfying (5.2)–(5.3). The theorem localizes the approximate solutions of the dual method to a neighborhood of $(\bar x, \bar y)$ where $L_r$ is smooth and strongly convex in $x$.
--
--   **Formalization Note** The paper's "inf $L_r(\cdot, y)$" is $g_r(y)$, the infimum over $X$, so (5.3) presupposes $x \in X$; we make $x \in X$ a hypothesis. (5.2) and (5.3) are differences in `EReal`; under the hypotheses $\sup g_r$ is finite, so they fail when $g_r(y) = -\infty$. "In fact (5.4)" is a local identity, stated as eventual equality of the two functions of $(x', y')$ near $(x, y)$; it is false globally. The Hessian form is the derivative of the gradient of $x' \mapsto L_r(x', y)$. Constraint indices are 0-based (`Fin m`).
-- source:
--   Rockafellar, A Dual Approach to Solving Nonlinear Programming Problems by Unconstrained Optimization, Math. Programming 5 (1973), pp. 368–369, Theorem 5.1 (i)–(iii), (5.2)–(5.4)

import Mathlib
import Definitions.Def_PenaltyLag_Rate_Basic

open Filter Topology

namespace PenaltyLag.Rate

/-- Theorem 5.1 (i)–(iii), pp. 368–369: for every r > 0 and β > 0 there are ε > 0 and α > 0 such
that whenever x ∈ X, sup g_r − g_r(y) ≤ ε (5.2) and L_r(x, y) − inf L_r(·, y) ≤ α (5.3):
(i) |y − ȳ| ≤ β, |x − x̄| ≤ β, x ∈ int X; (ii) L_r is C² in (x, y) at (x, y) and agrees near
(x, y) with the right side of (5.4); (iii) ∇²_x L_r(x, y) is positive definite. -/
theorem theorem_5_1_local
    {n m : ℕ} (X : Set (Pt n)) (hX : Convex ℝ X)
    (f₀ : Pt n → ℝ) (f : Fin m → Pt n → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (xbar : Pt n) (ybar : Mult m) (hA : Sec5Assumptions X f₀ f xbar ybar)
    (r : ℝ) (hr : 0 < r) (β : ℝ) (hβ : 0 < β) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ α : ℝ, 0 < α ∧ ∀ (y : Mult m) (x : Pt n), x ∈ X →
      (⨆ y' : Mult m, gr X f₀ f r y') - gr X f₀ f r y ≤ (ε : EReal) →
      (Lr f₀ f r x y : EReal) - gr X f₀ f r y ≤ (α : EReal) →
      (‖y - ybar‖ ≤ β ∧ ‖x - xbar‖ ≤ β ∧ x ∈ interior X) ∧
      ContDiffAt ℝ 2 (fun p : Pt n × Mult m => Lr f₀ f r p.1 p.2) (x, y) ∧
      ((fun p : Pt n × Mult m => Lr f₀ f r p.1 p.2) =ᶠ[𝓝 (x, y)]
        fun p : Pt n × Mult m =>
          f₀ p.1 + ∑ i ∈ activeSet f xbar, (p.2 i * f i p.1 + r * f i p.1 ^ 2)
            - (1 / (4 * r)) * ∑ i ∈ (activeSet f xbar)ᶜ, p.2 i ^ 2) ∧
      ∀ z : Pt n, z ≠ 0 → 0 < hessForm (fun x' => Lr f₀ f r x' y) x z := by sorry

end PenaltyLag.Rate
