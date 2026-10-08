-- Prove2me | Theorems.Thm_PenaltyLag_Rate_unique_solutions
-- name    : PenaltyLag.Rate.unique_solutions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:44:54.363981+00:00
-- url     : https://prove2.me/theorems/08ed9064-4c54-44d6-bd4e-cdd649b643aa
-- title:
--   §5 after (5.1) — x̄ is the unique optimal solution to (P), ȳ the only Kuhn–Tucker vector and the unique optimal solution to every dual problem
-- statement:
--   Let $X \subset \mathbb R^n$ be convex, let $f_0, f_1, \dots, f_m$ be convex on $X$, and let $(\bar x, \bar y)$ satisfy the standing assumptions of §5: $\bar x \in \operatorname{int} X$ is an optimal solution to (P), the $f_i$ are $C^2$ near $\bar x$, $\bar y$ satisfies with $\bar x$ the Kuhn–Tucker conditions, and (i) strict complementarity on the active set $I$, (ii) linear independence of $\nabla f_i(\bar x)$, $i \in I$, and (iii) the second-order condition $z \cdot H(\bar x, \bar y) z > 0$ on the tangent subspace hold. Then:
--
--   1. $\bar x$ is the **unique** optimal solution to (P): a point $x$ is an optimal solution to (P) if and only if $x = \bar x$;
--   2. for $r = 0$ and every $r > 0$, $\bar y$ is the **only** Kuhn–Tucker vector relative to $L_0$ or $L_r$, respectively, i.e. $y$ satisfies
--   $$
--   -\infty < \inf_{x \in X} L_r(x, y) = \inf \text{ in (P)}
--   $$
--   if and only if $y = \bar y$;
--   3. for $r = 0$ and every $r > 0$, $\bar y$ is the **unique** optimal solution to the dual problem $(D_r)$: $g_r(y') \le g_r(y)$ for all $y'$ holds if and only if $y = \bar y$.
--
--   This is what makes the limits $x^k \to \bar x$, $y^k \to \bar y$ of Corollary 5.2 meaningful: without uniqueness a maximizing dual sequence could approach a set of dual solutions rather than a point.
--
--   **Formalization Note** The paper's "dual problems $(D_r)$" includes the ordinary dual $(D_0)$, which uses the separate definitions $L_0$ and $g_0$. Both dual objectives and the infimum in (P) are in `EReal`. Convexity of $X$ and the $f_i$ (p. 358) is an explicit hypothesis.
-- source:
--   Rockafellar, A Dual Approach to Solving Nonlinear Programming Problems by Unconstrained Optimization, Math. Programming 5 (1973), p. 368, §5, paragraph after (5.1)

import Mathlib
import Definitions.Def_PenaltyLag_Rate_Basic

open Filter Topology

namespace PenaltyLag.Rate

/-- §5, p. 368, after (5.1): under the §5 assumptions x̄ is the unique optimal solution to (P),
and ȳ is the only Kuhn–Tucker vector and unique dual optimizer for (D₀) and every (D_r), r > 0. -/
theorem unique_solutions
    {n m : ℕ} (X : Set (Pt n)) (hX : Convex ℝ X)
    (f₀ : Pt n → ℝ) (f : Fin m → Pt n → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (xbar : Pt n) (ybar : Mult m) (hA : Sec5Assumptions X f₀ f xbar ybar) :
    (∀ x : Pt n, IsPrimalOptimal X f₀ f x ↔ x = xbar) ∧
    (∀ y : Mult m, IsKTVector0 X f₀ f y ↔ y = ybar) ∧
    (∀ y : Mult m, (∀ y' : Mult m, g0 X f₀ f y' ≤ g0 X f₀ f y) ↔ y = ybar) ∧
    ∀ r : ℝ, 0 < r →
      (∀ y : Mult m, IsKTVector X f₀ f r y ↔ y = ybar) ∧
      (∀ y : Mult m, (∀ y' : Mult m, gr X f₀ f r y' ≤ gr X f₀ f r y) ↔ y = ybar) := by sorry

end PenaltyLag.Rate
