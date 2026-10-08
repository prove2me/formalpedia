-- Prove2me | Theorems.Thm_PenaltyLag_Exact_corollary_3_4_r0
-- name    : PenaltyLag.Exact.corollary_3_4_r0
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:48:38.914648+00:00
-- url     : https://prove2.me/theorems/39613051-7d79-490c-aa04-c78b3b572bd7
-- title:
--   Corollary 3.4 ($r = 0$) — $(\bar x, \bar y)$ is a saddle point of $L_0$ iff the ordinary Kuhn–Tucker conditions hold
-- statement:
--   Let $X$ be a nonempty convex subset of a real vector space $E$ and $f_0, f_1, \dots, f_m$ convex functions on $X$, defining the convex program (P), and let $L_0$ be its ordinary Lagrangian (3.2): $L_0(x, y) = f_0(x) + \sum_i y_i f_i(x)$ if $y \ge 0$ and $-\infty$ otherwise. For $\bar x \in E$ and $\bar y \in \mathbb R^m$, the pair $(\bar x, \bar y)$ is a saddle point of $L_0$ on $X \times \mathbb R^m$,
--   $$
--   \bar x \in X, \qquad L_0(\bar x, y) \le L_0(\bar x, \bar y) \le L_0(x, \bar y) \quad \text{for all } x \in X,\ y \in \mathbb R^m,
--   $$
--   if and only if the ordinary Kuhn–Tucker conditions hold: (i) $\bar y_i \ge 0$, $f_i(\bar x) \le 0$, $\bar y_i f_i(\bar x) = 0$ for $i = 1, \dots, m$, and (ii) $\bar x$ minimizes $f_0 + \sum_{i=1}^m \bar y_i f_i$ over $X$.
--
--   This is the case $r = 0$ of Corollary 3.4, the classical saddle-point form of the Kuhn–Tucker conditions.
--
--   **Formalization Note** The standing assumption of p. 358 is a hypothesis. $L_0$ is extended-real valued and the inequalities are in the extended reals; $y$ ranges over all of $\mathbb R^m$, with $L_0 = -\infty$ off the nonnegative orthant as in (3.2).
-- source:
--   Rockafellar, A Dual Approach to Solving Nonlinear Programming Problems by Unconstrained Optimization, Math. Programming 5 (1973), p. 362, Corollary 3.4 (case r = 0)

import Mathlib
import Definitions.Def_PenaltyLag_Exact_Basic

namespace PenaltyLag.Exact

/-- Corollary 3.4, p. 362, the case r = 0: (x̄, ȳ) is a saddle point of the ordinary
Lagrangian L₀ iff the ordinary Kuhn–Tucker conditions hold. -/
theorem corollary_3_4_r0 {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (X : Set E) (hX : Convex ℝ X) (hXne : X.Nonempty)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (xbar : E) (ybar : PenaltyLag.Asymptotic.Mult m) :
    IsSaddle0 X f₀ f xbar ybar ↔ KuhnTuckerConditions X f₀ f xbar ybar := by sorry

end PenaltyLag.Exact
