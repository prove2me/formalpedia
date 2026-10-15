-- Prove2me | Theorems.Thm_PrizeAlloc_Interval_theorem_1_step_1
-- name    : PrizeAlloc.Interval.theorem_1_step_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:29:38.693528+00:00
-- url     : https://prove2.me/theorems/e32fa877-fd7d-497a-8c4c-36fc3737d980
-- title:
--   Theorem 1, Step 1 (p. 28) — a two-competitor allocation (x₁, x₂) forces (x₁, x₁) at 2x₁ or (x₂, x₂) at 2x₂
-- statement:
--   Let $U$ be a countable set of at least three potential competitors and $\varphi$ a prize allocation rule satisfying order preservation, endowment monotonicity and consistency. Let $N = \{1, 2\}$ be two competitors ranked $\mathcal R(1) = 1$, $\mathcal R(2) = 2$. If $x_1, x_2 \ge 0$ and
--   $$\varphi(N, \mathcal R, x_1 + x_2) = (x_1, x_2),$$
--   then
--   $$\varphi(N, \mathcal R, x_1 + x_1) = (x_1, x_1) \quad \text{or} \quad \varphi(N, \mathcal R, x_2 + x_2) = (x_2, x_2).$$
--
--   This is display (3) ⇒ (4) of the proof of Theorem 1: every point of the two-competitor allocation path is joined to the diagonal along a horizontal or a vertical segment, which is what makes the path a staircase of intervals.
--
--   **Formalization Note** The two competitors are distinct elements $u, v$ of $U$ and the ranking is the list $[u, v]$. The hypotheses $x_1, x_2 \ge 0$ restate that $x_1, x_2$ are prizes at the endowment $x_1 + x_2 \ge 0$.
-- source:
--   Dietzenbacher and Kondratev, Fair and Consistent Prize Allocation in Competitions, arXiv:2008.08985v2, p. 28, proof of Theorem 1, Step 1, displays (3)–(4)

import Mathlib
import Definitions.Def_PrizeAlloc_Interval_Setting

namespace PrizeAlloc.Interval

theorem theorem_1_step_1 {U : Type*} [DecidableEq U] [Countable U]
    (hU : ∃ a b c : U, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (φ : List U → ℝ → U → ℝ) (hφ : IsPrizeRule φ)
    (hOP : OrderPreserving φ) (hEM : EndowmentMonotone φ) (hCons : Consistent φ)
    (u v : U) (huv : u ≠ v) (x₁ x₂ : ℝ) (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂)
    (h3 : φ [u, v] (x₁ + x₂) u = x₁ ∧ φ [u, v] (x₁ + x₂) v = x₂) :
    (φ [u, v] (x₁ + x₁) u = x₁ ∧ φ [u, v] (x₁ + x₁) v = x₁) ∨
      (φ [u, v] (x₂ + x₂) u = x₂ ∧ φ [u, v] (x₂ + x₂) v = x₂) := by sorry

end PrizeAlloc.Interval
