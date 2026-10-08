-- Prove2me | Theorems.Thm_PenaltyLag_Exact_corollary_3_4
-- name    : PenaltyLag.Exact.corollary_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:49:07.67299+00:00
-- url     : https://prove2.me/theorems/8c9e3f82-115b-4365-be81-20e05312d138
-- title:
--   Corollary 3.4 ($r > 0$) — $L_r$ and $L_0$ have the same Kuhn–Tucker vectors and saddle points; saddle points are the Kuhn–Tucker pairs
-- statement:
--   Let $X$ be a nonempty convex subset of a real vector space $E$ and $f_0, f_1, \dots, f_m$ convex functions on $X$, defining the convex program (P). Let $r > 0$, $\bar x \in E$ and $\bar y \in \mathbb R^m$. Then:
--
--   1. $\bar y$ is a Kuhn–Tucker vector relative to $L_r$ if and only if it is a Kuhn–Tucker vector relative to the ordinary Lagrangian $L_0$;
--   2. $(\bar x, \bar y)$ is a saddle point of $L_r$ on $X \times \mathbb R^m$ if and only if it is a saddle point of $L_0$ on $X \times \mathbb R^m$;
--   3. $(\bar x, \bar y)$ is a saddle point of $L_r$ if and only if the ordinary Kuhn–Tucker conditions hold:
--   $$
--   \text{(i)}\ \ \bar y_i \ge 0,\ \ f_i(\bar x) \le 0,\ \ \bar y_i f_i(\bar x) = 0 \ \ (i = 1, \dots, m); \qquad \text{(ii)}\ \ \bar x \in X \text{ minimizes } f_0 + \textstyle\sum_{i=1}^m \bar y_i f_i \text{ over } X.
--   $$
--
--   Comparing every $r > 0$ with $r = 0$ gives the paper's "relative to the Lagrangians $L_r$, $r \ge 0$, one has the same Kuhn–Tucker vectors and saddle points"; the case $r = 0$ of item 3 is a separate statement of this mission. The corollary shows what $L_r$, $r > 0$, has in common with $L_0$.
--
--   **Formalization Note** The standing assumption of p. 358 is a hypothesis. A Kuhn–Tucker vector relative to $L_0$ is (3.17) with $L_0$ in place of $L_r$; since $L_0(x, y) = -\infty$ for $y \not\ge 0$, it is automatically nonnegative. Saddle points of $L_0$ are compared in the extended reals.
-- source:
--   Rockafellar, A Dual Approach to Solving Nonlinear Programming Problems by Unconstrained Optimization, Math. Programming 5 (1973), p. 362, Corollary 3.4 (case r > 0)

import Mathlib
import Definitions.Def_PenaltyLag_Exact_Basic

namespace PenaltyLag.Exact

/-- Corollary 3.4, p. 362 (r > 0 against r = 0): L_r and L₀ have the same Kuhn–Tucker
vectors and the same saddle points, and (x̄, ȳ) is a saddle point of L_r iff the ordinary
Kuhn–Tucker conditions hold. -/
theorem corollary_3_4 {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (X : Set E) (hX : Convex ℝ X) (hXne : X.Nonempty)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (r : ℝ) (hr : 0 < r) (xbar : E) (ybar : PenaltyLag.Asymptotic.Mult m) :
    (IsKTVector X f₀ f r ybar ↔ IsKTVector0 X f₀ f ybar) ∧
    (IsSaddle X f₀ f r xbar ybar ↔ IsSaddle0 X f₀ f xbar ybar) ∧
    (IsSaddle X f₀ f r xbar ybar ↔ KuhnTuckerConditions X f₀ f xbar ybar) := by sorry

end PenaltyLag.Exact
