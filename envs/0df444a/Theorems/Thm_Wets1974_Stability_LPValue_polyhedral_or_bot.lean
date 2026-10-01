-- Prove2me | Theorems.Thm_Wets1974_Stability_LPValue_polyhedral_or_bot
-- name    : Wets1974.Stability.LPValue_polyhedral_or_bot
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T14:34:47.521875+00:00
-- url     : https://prove2.me/theorems/5827cfcb-e86a-4bf9-a328-44c13eee771f
-- title:
--   Corollary 7.3 — the LP value function is finite convex polyhedral on pos A, or identically −∞
-- statement:
--   Let $A$ be a real $m\times n$ matrix and $c\in\mathbb R^n$ a row vector. For $t\in\mathbb R^m$ let
--   $$Q(t)=\min\{cx \mid Ax=t,\ x\ge 0\}\in[-\infty,+\infty]$$
--   (with $+\infty$ for an infeasible and $-\infty$ for an unbounded program), and let $\operatorname{pos}A=\{Ax: x\ge 0\}$. Then exactly the following dichotomy holds:
--
--   1. either $Q$ is a **finite convex polyhedral function on $\operatorname{pos}A$**: there are finitely many affine functions $a_0,\dots,a_k$ on $\mathbb R^m$ with
--   $$Q(t)=\max_{0\le i\le k}a_i(t)\in\mathbb R\qquad\text{for every }t\in\operatorname{pos}A;$$
--   2. or $Q(t)=-\infty$ for **every** $t\in\operatorname{pos}A$.
--
--   In the paper's words, $Q$ is finite convex polyhedral on $\operatorname{pos}A$ unless $Q(t)=-\infty$ for some $t\in\operatorname{pos}A$, in which case it is identically $-\infty$ there. This is the parametric-LP fact that makes the recourse function $Q(x,\xi)$ piecewise linear in its right-hand side, and it drives Proposition 7.5 and Theorem 7.6.
--
--   **Formalization Note** $Q$ is the platform definition `KallMayer.Recourse.LPValue A c t`. The paper's Theorem 7.2 assumes $A$ has rank $m$; Corollary 7.3 holds without it, and this statement omits it, which makes it stronger. "Convex polyhedral" is read as the maximum of finitely many affine functions (see the definition file); the paper never defines it.
-- source:
--   Wets, Stochastic Programs with Fixed Recourse: The Equivalent Deterministic Program, SIAM Review 16(3), 1974, p. 328, Corollary 7.3

import Mathlib
import Definitions.Def_KallMayer_Recourse_LPValue
import Definitions.Def_Wets1974_Stability_ConvexAnalysis

namespace Wets1974.Stability

/-- Corollary 7.3, p. 328: the value function `Q(t) = min {c x | A x = t, x ≥ 0}` is a finite
convex polyhedral function on `pos A`, unless `Q(t) = −∞` for some `t ∈ pos A`, in which case
it is identically `−∞` on `pos A`. -/
theorem LPValue_polyhedral_or_bot {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) :
    IsFiniteConvexPolyhedralOn (fun t => KallMayer.Recourse.LPValue A c t) (posCone A) ∨
      ∀ t ∈ posCone A, KallMayer.Recourse.LPValue A c t = ⊥ := by sorry

end Wets1974.Stability
