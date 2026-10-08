-- Prove2me | Theorems.Thm_PenaltyLag_Exact_theorem_3_5
-- name    : PenaltyLag.Exact.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:48:51.808573+00:00
-- url     : https://prove2.me/theorems/a3a9d536-4936-4cef-85ee-8742bb7014ad
-- title:
--   Theorem 3.5 — for normal (P), dual optimal $\bar y$ and $r > 0$: $\bar x$ is optimal iff $\bar x$ minimizes $L_r(\cdot, \bar y)$ over $X$
-- statement:
--   Let $X$ be a nonempty convex subset of a real vector space $E$ and $f_0, f_1, \dots, f_m$ convex functions on $X$, defining the convex program
--   $$
--   \text{(P)}\qquad \text{minimize } f_0(x) \text{ over } x \in X \text{ subject to } f_i(x) \le 0,\ i = 1, \dots, m.
--   $$
--   For $r > 0$ let $L_r(x, y) = f_0(x) + \frac{1}{4r}\sum_{i=1}^m [\theta(y_i + 2 r f_i(x))^2 - y_i^2]$, $\theta(t) = \max\{0, t\}$, be the penalty Lagrangian and $g_r(y) = \inf_{x \in X} L_r(x, y)$ the dual objective. Assume that (P) is normal (its optimal value equals the dual optimal value) and that $\bar y \in \mathbb R^m$ is a dual optimal solution. Let $r > 0$. Then for every $\bar x \in E$,
--   $$
--   \bar x \text{ is an optimal solution to (P)} \iff \bar x \in X \ \text{ and } \ L_r(\bar x, \bar y) \le L_r(x, \bar y) \ \text{ for all } x \in X.
--   $$
--
--   The theorem says that, once a dual optimal $\bar y$ is known, the constrained problem (P) reduces to the minimization of $L_r(\cdot, \bar y)$ over $X$, with no constraints $f_i(x) \le 0$: every minimizer is optimal. This fails for the ordinary Lagrangian $L_0$ ($r = 0$), whose minimizers at $\bar y$ may include points that are not even feasible; the paper names this absence as a serious impediment to computational approaches based on duality.
--
--   **Formalization Note** The standing assumption of p. 358 (convex $X \ne \emptyset$, convex $f_i$) is a hypothesis. The paper's "dual optimal solution" is optimal for $(D_0)$, equivalently for every $(D_r)$ (Theorem 3.2, p. 359); here it is taken as optimal for $(D_r)$ with the same $r$, $g_r(\bar y) = \sup_y g_r(y) > -\infty$, which is the form the proof uses. Normality is $\sup_y g_0(y) = \inf$ in (P) in the extended reals. $r > 0$ is essential and explicit. $\bar x$ ranges over all of $E$ and no sign restriction is placed on $\bar y$.
-- source:
--   Rockafellar, A Dual Approach to Solving Nonlinear Programming Problems by Unconstrained Optimization, Math. Programming 5 (1973), p. 362, Theorem 3.5

import Mathlib
import Definitions.Def_PenaltyLag_Exact_Basic

namespace PenaltyLag.Exact

/-- Theorem 3.5, p. 362: if (P) is normal, ȳ is a dual optimal solution and r > 0, then
x̄ is an optimal solution to (P) iff x̄ minimizes L_r(·, ȳ) over X. -/
theorem theorem_3_5 {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (X : Set E) (hX : Convex ℝ X) (hXne : X.Nonempty)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (r : ℝ) (hr : 0 < r) (hnormal : IsNormal X f₀ f)
    (ybar : PenaltyLag.Asymptotic.Mult m) (hybar : IsDualOptimal X f₀ f r ybar) (xbar : E) :
    IsOptimal X f₀ f xbar ↔ (xbar ∈ X ∧ ∀ x ∈ X, PenaltyLag.Asymptotic.Lr f₀ f r xbar ybar ≤ PenaltyLag.Asymptotic.Lr f₀ f r x ybar) := by sorry

end PenaltyLag.Exact
