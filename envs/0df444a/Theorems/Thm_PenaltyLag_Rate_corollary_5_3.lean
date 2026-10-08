-- Prove2me | Theorems.Thm_PenaltyLag_Rate_corollary_5_3
-- name    : PenaltyLag.Rate.corollary_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:45:56.713278+00:00
-- url     : https://prove2.me/theorems/bcd57e76-531b-4838-8a69-cb6cd7dcd134
-- title:
--   Corollary 5.3 — if αₖ ≤ q[sup g_r − g_r(yᵏ)] eventually, then |xᵏ − x̄| ≤ s|yᵏ − ȳ| eventually
-- statement:
--   Let $X \subset \mathbb R^n$ be convex and $f_0, f_1, \dots, f_m$ convex on $X$, and let $(\bar x, \bar y)$ satisfy the standing assumptions of §5: $\bar x \in \operatorname{int} X$ is an optimal solution to (P), the $f_i$ are $C^2$ near $\bar x$, $\bar y$ satisfies with $\bar x$ the Kuhn–Tucker conditions, $\bar y_i \ne 0$ on the active set $I$, the gradients $\nabla f_i(\bar x)$, $i \in I$, are linearly independent, and $z \cdot H(\bar x, \bar y) z > 0$ for every nonzero $z$ orthogonal to them.
--
--   Let $r > 0$, let $\{y^k\}$ be a bounded maximizing sequence for $(D_r)$, and let $x^k \in X$ satisfy
--   $$
--   L_r(x^k, y^k) - g_r(y^k) \le \alpha_k \qquad (4.7)
--   $$
--   with $\alpha_k \to 0$. Suppose that for some $q > 0$
--   $$
--   \alpha_k \le q\,[\sup g_r - g_r(y^k)] \quad \text{for all sufficiently large } k. \qquad (5.18)
--   $$
--   Then there is a constant $s > 0$ such that
--   $$
--   |x^k - \bar x| \le s\,|y^k - \bar y| \quad \text{for all sufficiently large } k. \qquad (5.19)
--   $$
--
--   This is the paper's rate statement: if the inner minimizations are carried out to a tolerance proportional to the current dual gap, the primal points converge to $\bar x$ at least as fast as the dual iterates converge to $\bar y$, whatever unconstrained method generates $\{y^k\}$.
--
--   **Formalization Note** "Suppose in Corollary 5.2" is spelled out as the hypotheses of Corollary 5.2, i.e. those of Theorem 4.1 under the §5 assumptions; Theorem 4.1's finiteness of the asymptotic optimal value is omitted as automatic. Convergence of $x^k$ and $y^k$ is not assumed. $\sup g_r$, $g_r(y^k)$ and the right side of (5.18) are computed in `EReal`; $\sup g_r$ is finite here, and (4.7) forces $g_r(y^k) > -\infty$. Both "$s > 0$" and "for all sufficiently large $k$" (an `atTop` eventually, with $s$ independent of $k$) are part of the conclusion.
-- source:
--   Rockafellar, A Dual Approach to Solving Nonlinear Programming Problems by Unconstrained Optimization, Math. Programming 5 (1973), p. 371, Corollary 5.3, (5.18)–(5.19)

import Mathlib
import Definitions.Def_PenaltyLag_Rate_Basic

open Filter Topology

namespace PenaltyLag.Rate

/-- Corollary 5.3, p. 371: in the setting of Corollary 5.2, if for some q > 0 the tolerances satisfy
αₖ ≤ q[sup g_r − g_r(yᵏ)] for all sufficiently large k (5.18), then there is a constant s > 0 with
|xᵏ − x̄| ≤ s|yᵏ − ȳ| for all sufficiently large k (5.19). -/
theorem corollary_5_3
    {n m : ℕ} (X : Set (Pt n)) (hX : Convex ℝ X)
    (f₀ : Pt n → ℝ) (f : Fin m → Pt n → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (xbar : Pt n) (ybar : Mult m) (hA : Sec5Assumptions X f₀ f xbar ybar)
    (r : ℝ) (hr : 0 < r)
    (y : ℕ → Mult m) (hyb : Bornology.IsBounded (Set.range y)) (hymax : IsMaximizing X f₀ f r y)
    (x : ℕ → Pt n) (hxX : ∀ k, x k ∈ X)
    (α : ℕ → ℝ) (hα : Tendsto α atTop (𝓝 0))
    (h47 : ∀ k, (Lr f₀ f r (x k) (y k) : EReal) - gr X f₀ f r (y k) ≤ (α k : EReal))
    (q : ℝ) (hq : 0 < q)
    (h518 : ∀ᶠ k in atTop,
      (α k : EReal) ≤ (q : EReal) * ((⨆ y' : Mult m, gr X f₀ f r y') - gr X f₀ f r (y k))) :
    ∃ s : ℝ, 0 < s ∧ ∀ᶠ k in atTop, ‖x k - xbar‖ ≤ s * ‖y k - ybar‖ := by sorry

end PenaltyLag.Rate
