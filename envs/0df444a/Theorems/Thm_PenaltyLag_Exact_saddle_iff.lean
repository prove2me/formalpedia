-- Prove2me | Theorems.Thm_PenaltyLag_Exact_saddle_iff
-- name    : PenaltyLag.Exact.saddle_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:48:48.293203+00:00
-- url     : https://prove2.me/theorems/5d4f36b4-d292-4ad9-8a3c-5b8a4ea501db
-- title:
--   §3, p. 362 — $(\bar x, \bar y)$ is a saddle point of $L_r$ iff $\bar x$ is optimal for (P) and $\bar y$ is a Kuhn–Tucker vector
-- statement:
--   Let $X$ be a nonempty convex subset of a real vector space $E$ and $f_0, f_1, \dots, f_m$ convex functions on $X$, defining the convex program (P). Let $r > 0$ and let $L_r$ be the penalty Lagrangian (2.3). For $\bar x \in E$ and $\bar y \in \mathbb R^m$, the pair $(\bar x, \bar y)$ is a saddle point of $L_r$ on $X \times \mathbb R^m$, that is, $\bar x \in X$ and
--   $$
--   L_r(\bar x, y) \le L_r(\bar x, \bar y) \le L_r(x, \bar y) \qquad \text{for all } x \in X,\ y \in \mathbb R^m,
--   $$
--   if and only if $\bar x$ is an optimal solution to (P) and $\bar y$ is a Kuhn–Tucker vector for (P) relative to $L_r$.
--
--   This is the penalty-Lagrangian counterpart of the classical saddle-point characterization of optimality, and the bridge used in the proof of Theorem 3.5.
--
--   **Formalization Note** The standing assumption of p. 358 (convex $X \ne \emptyset$, convex $f_i$) is a hypothesis. The pair is arbitrary: if $\bar x \notin X$ both sides fail. Saddle points are in the sense of Rockafellar's *Convex Analysis*, §36 (minimum over $x \in X$, maximum over $y \in \mathbb R^m$, no sign restriction on $y$).
-- source:
--   Rockafellar, A Dual Approach to Solving Nonlinear Programming Problems by Unconstrained Optimization, Math. Programming 5 (1973), §3, p. 362 (sentence before Corollary 3.4)

import Mathlib
import Definitions.Def_PenaltyLag_Exact_Basic

namespace PenaltyLag.Exact

/-- §3, p. 362: for r > 0, (x̄, ȳ) is a saddle point of L_r iff x̄ is an optimal solution
to (P) and ȳ is a Kuhn–Tucker vector relative to L_r. -/
theorem saddle_iff {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (X : Set E) (hX : Convex ℝ X) (hXne : X.Nonempty)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (r : ℝ) (hr : 0 < r) (xbar : E) (ybar : PenaltyLag.Asymptotic.Mult m) :
    IsSaddle X f₀ f r xbar ybar ↔ (IsOptimal X f₀ f xbar ∧ IsKTVector X f₀ f r ybar) := by sorry

end PenaltyLag.Exact
