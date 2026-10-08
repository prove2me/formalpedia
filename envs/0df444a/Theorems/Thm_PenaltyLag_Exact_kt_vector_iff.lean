-- Prove2me | Theorems.Thm_PenaltyLag_Exact_kt_vector_iff
-- name    : PenaltyLag.Exact.kt_vector_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:48:42.577676+00:00
-- url     : https://prove2.me/theorems/41f030fd-6687-4da2-bb57-3c9e24461c3a
-- title:
--   §3 after (3.17) — $\bar y$ is a Kuhn–Tucker vector for $L_r$ iff $\bar y$ is optimal for $(D_r)$ and (P) is normal
-- statement:
--   Let $X$ be a nonempty convex subset of a real vector space $E$ and $f_0, f_1, \dots, f_m$ convex functions on $X$, defining the convex program (P). Let $r > 0$, let $L_r$ be the penalty Lagrangian (2.3), $g_r(y) = \inf_{x \in X} L_r(x, y)$ the objective of the dual problem $(D_r)$, and let $\bar y \in \mathbb R^m$. Then $\bar y$ is a Kuhn–Tucker vector for (P) relative to $L_r$, that is,
--   $$
--   -\infty < \inf_{x \in X} L_r(x, \bar y) = \inf \text{ in (P)},
--   $$
--   if and only if $\bar y$ is an optimal solution to $(D_r)$ and (P) is normal (the dual optimal value $\sup_y g_0(y)$ equals the optimal value of (P)).
--
--   Together with the fact that $(D_r)$ and $(D_0)$ have the same optimal solutions, this shows that the notion of Kuhn–Tucker vector does not depend on $r$. It is the step that turns the hypotheses of Theorem 3.5 (normality and dual optimality) into a Kuhn–Tucker vector.
--
--   **Formalization Note** The paper states the standing assumption (convexity of $X$ and the $f_i$, $X \ne \emptyset$) once on p. 358; here it is a hypothesis. "Optimal solution to $(D_r)$" means $g_r(\bar y) = \sup_y g_r(y)$ with $g_r(\bar y) > -\infty$ (the convention of p. 361). Infima and suprema are taken in the extended reals; indices are 0-based (`Fin m`).
-- source:
--   Rockafellar, A Dual Approach to Solving Nonlinear Programming Problems by Unconstrained Optimization, Math. Programming 5 (1973), §3, after (3.17), pp. 361–362

import Mathlib
import Definitions.Def_PenaltyLag_Exact_Basic

namespace PenaltyLag.Exact

/-- §3 after (3.17), pp. 361–362: for r > 0, ȳ is a Kuhn–Tucker vector relative to L_r
iff ȳ is an optimal solution to (D_r) and (P) is normal. -/
theorem kt_vector_iff {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (X : Set E) (hX : Convex ℝ X) (hXne : X.Nonempty)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (r : ℝ) (hr : 0 < r) (ybar : PenaltyLag.Asymptotic.Mult m) :
    IsKTVector X f₀ f r ybar ↔ (IsDualOptimal X f₀ f r ybar ∧ IsNormal X f₀ f) := by sorry

end PenaltyLag.Exact
