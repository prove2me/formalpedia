-- Prove2me | Theorems.Thm_PenaltyLag_Rate_corollary_5_2_limits
-- name    : PenaltyLag.Rate.corollary_5_2_limits
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:44:47.873043+00:00
-- url     : https://prove2.me/theorems/e0a24e6d-9859-472a-9368-5cd021d27b0b
-- title:
--   Corollary 5.2, (5.14) — sequences generated as in Theorem 4.1 converge: xᵏ → x̄, yᵏ → ȳ
-- statement:
--   Assume the standing assumptions of §5 for $(\bar x, \bar y)$, with $X \subset \mathbb R^n$ convex and $f_0, \dots, f_m$ convex on $X$. Let $r > 0$, let $\{y^k\}$ be a bounded maximizing sequence for $(D_r)$, i.e. $g_r(y^k) \to \sup g_r$, and for each $k$ let $x^k \in X$ satisfy
--   $$
--   L_r(x^k, y^k) - \inf_X L_r(\cdot, y^k) = L_r(x^k, y^k) - g_r(y^k) \le \alpha_k, \qquad (4.7)
--   $$
--   where $\alpha_k \to 0$ (the scheme of Theorem 4.1). Then
--   $$
--   \lim_{k \to \infty} x^k = \bar x, \qquad \lim_{k \to \infty} y^k = \bar y. \qquad (5.14)
--   $$
--
--   Under the second-order conditions the asymptotically minimizing sequence produced by Theorem 4.1 therefore converges to the unique primal optimum, and the dual iterates converge to the unique multiplier.
--
--   **Formalization Note** "Generated as in Theorem 4.1" is spelled out as the hypotheses of that theorem. Its assumption that the asymptotic optimal value in (P) is finite is omitted because it holds automatically here (a Kuhn–Tucker vector exists). The maximizing property and (4.7) are stated in `EReal`; (4.7) forces $g_r(y^k) > -\infty$. Convexity (p. 358) is an explicit hypothesis.
-- source:
--   Rockafellar, A Dual Approach to Solving Nonlinear Programming Problems by Unconstrained Optimization, Math. Programming 5 (1973), p. 370, Corollary 5.2, (5.14); setting of Theorem 4.1, (4.7), p. 365

import Mathlib
import Definitions.Def_PenaltyLag_Rate_Basic

open Filter Topology

namespace PenaltyLag.Rate

/-- Corollary 5.2, (5.14), p. 370: under the §5 assumptions, if {yᵏ} is a bounded maximizing
sequence for (D_r), r > 0, and xᵏ ∈ X satisfy L_r(xᵏ, yᵏ) − g_r(yᵏ) ≤ αₖ (4.7) with αₖ → 0
(the setting of Theorem 4.1), then xᵏ → x̄ and yᵏ → ȳ. -/
theorem corollary_5_2_limits
    {n m : ℕ} (X : Set (Pt n)) (hX : Convex ℝ X)
    (f₀ : Pt n → ℝ) (f : Fin m → Pt n → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (xbar : Pt n) (ybar : Mult m) (hA : Sec5Assumptions X f₀ f xbar ybar)
    (r : ℝ) (hr : 0 < r)
    (y : ℕ → Mult m) (hyb : Bornology.IsBounded (Set.range y)) (hymax : IsMaximizing X f₀ f r y)
    (x : ℕ → Pt n) (hxX : ∀ k, x k ∈ X)
    (α : ℕ → ℝ) (hα : Tendsto α atTop (𝓝 0))
    (h47 : ∀ k, (Lr f₀ f r (x k) (y k) : EReal) - gr X f₀ f r (y k) ≤ (α k : EReal)) :
    Tendsto x atTop (𝓝 xbar) ∧ Tendsto y atTop (𝓝 ybar) := by sorry

end PenaltyLag.Rate
