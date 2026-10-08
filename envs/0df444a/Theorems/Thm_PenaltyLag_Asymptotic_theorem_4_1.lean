-- Prove2me | Theorems.Thm_PenaltyLag_Asymptotic_theorem_4_1
-- name    : PenaltyLag.Asymptotic.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:44:44.024807+00:00
-- url     : https://prove2.me/theorems/bf19caa3-cb09-448a-89d4-afce34e672b6
-- title:
--   Theorem 4.1 — approximate minimizers of $L_r(\cdot, y^k)$ along a bounded maximizing dual sequence are asymptotically minimizing
-- statement:
--   Throughout, $X$ is a nonempty convex subset of a real vector space $E$ and $f_0, f_1, \dots, f_m : X \to \mathbb R$ are convex (the paper's standing assumption of §3, p. 358). Suppose the asymptotic optimal value in (P) is finite. Let $r > 0$, let $\{y^k\}$ be a bounded maximizing sequence for $(D_r)$, i.e. $g_r(y^k) \to \sup_{y \in \mathbb R^m} g_r(y)$, and for each $k$ let $x^k \in X$ satisfy
--   $$
--   L_r(x^k, y^k) - \inf_{x \in X} L_r(x, y^k) = L_r(x^k, y^k) - g_r(y^k) \le \alpha_k, \tag{4.7}
--   $$
--   where $\alpha_k \to 0$. Then $\{x^k\}$ is an asymptotically minimizing sequence for (P): $\limsup_k f_i(x^k) \le 0$ for every $i$, and $\limsup_k f_0(x^k)$ equals the asymptotic optimal value in (P).
--
--   This is the paper's headline result: any method that maximizes the smooth, unconstrained dual $g_r$ over all of $\mathbb R^m$, using only approximate minimizations of $L_r(\cdot, y^k)$, produces an asymptotically optimal primal sequence, with no constraint qualification and no assumption that (P) has feasible or optimal solutions.
--
--   **Formalization Note** (4.7) is written $L_r(x^k, y^k) \le g_r(y^k) + \alpha_k$ in `EReal`, equivalent to the printed difference because $L_r(x^k, y^k)$ is real and $g_r(y^k) < +\infty$; it avoids `EReal` subtraction. Only $\alpha_k \to 0$ is assumed (nonnegativity follows from (4.7)). "Maximizing" is convergence in `EReal` to the supremum over all of $\mathbb R^m$, with no sign restriction on $y$; "bounded" is boundedness of $\{y^k\}$ in $\mathbb R^m$; "finite" is $\ne \pm\infty$ in `EReal`. The paper's functions $f_i : X \to \mathbb R$ are total functions $E \to \mathbb R$ convex on $X$, and only their values on $X$ enter; constraint indices are `Fin m` (0-based, the paper's $1, \dots, m$), and $f_0$ is a separate argument; the standing assumption (p. 358: $X$ nonempty convex, $f_i$ convex) is a hypothesis even where the statement does not repeat it.
-- source:
--   Rockafellar, A Dual Approach to Solving Nonlinear Programming Problems by Unconstrained Optimization, Math. Programming 5 (1973), p. 365, Theorem 4.1, (4.7)

import Mathlib
import Definitions.Def_PenaltyLag_Asymptotic_Basic

open Filter Topology

namespace PenaltyLag.Asymptotic

/-- Theorem 4.1 (p. 365): if the asymptotic optimal value in (P) is finite, {yᵏ} is a bounded
maximizing sequence for (D_r), r > 0, and xᵏ ∈ X satisfies L_r(xᵏ, yᵏ) − g_r(yᵏ) ≤ αₖ (4.7) with
αₖ → 0, then {xᵏ} is an asymptotically minimizing sequence for (P). -/
theorem theorem_4_1 {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (X : Set E) (hX : Convex ℝ X) (hXne : X.Nonempty)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (hfin : asympValue X f₀ f ≠ ⊥ ∧ asympValue X f₀ f ≠ ⊤)
    (r : ℝ) (hr : 0 < r)
    (y : ℕ → Mult m) (hyb : Bornology.IsBounded (Set.range y)) (hymax : IsMaximizing X f₀ f r y)
    (x : ℕ → E) (hxX : ∀ k, x k ∈ X)
    (α : ℕ → ℝ) (hα : Tendsto α atTop (𝓝 0))
    (h47 : ∀ k, (Lr f₀ f r (x k) (y k) : EReal) ≤ gr X f₀ f r (y k) + (α k : EReal)) :
    IsAsympMinimizing X f₀ f x := by sorry

end PenaltyLag.Asymptotic
