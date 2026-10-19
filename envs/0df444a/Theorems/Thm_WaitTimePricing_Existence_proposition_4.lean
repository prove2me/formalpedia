-- Prove2me | Theorems.Thm_WaitTimePricing_Existence_proposition_4
-- name    : WaitTimePricing.Existence.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T11:26:30.756993+00:00
-- url     : https://prove2.me/theorems/bad85f44-305e-4c51-9e2f-afd97d098958
-- title:
--   Proposition 4 — $V^g_N$ is concave and $K^g_N$ decreases on $[0,\bar w+C]$
-- statement:
--   For every $g\ge 0$ and every $N\ge 1$, the function $V^g_N$ produced by Algorithm 1 is concave on $[0,\bar w+C]$, and the slope adjustment $K^g_N$ is nonincreasing on $[0,\bar w+C]$.
--
--   Consequently the slope of $V^g_N$ is smallest, $-g$, at $\bar w$ and largest, $-g+K^g_N(0)$, at $0$.
--
--   **Formalization Note** "$N\in\mathbb N$" means $N\ge1$ (the grid step is $\bar w/N$). $K^g_N$ is a step function, so "decreases" means nonincreasing.
-- source:
--   Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 14, Proposition 4

import Mathlib
import Definitions.Def_WaitTimePricing_Existence_Setting
import Definitions.Def_WaitTimePricing_Existence_Algorithm1

namespace WaitTimePricing.Existence

open Set Filter

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 14, Proposition 4.

Given `g ≥ 0` and `N ∈ ℕ`, `V^g_N(w)` is concave in `w` and `K^g_N(w)` decreases in `w` for all
`w ∈ [0, w̄ + C]`.

**Formalization Note.** `N ∈ ℕ` means `N ≥ 1` (`ε_N = w̄/N`). `K^g_N` is a step function, so
"decreases" is `AntitoneOn` (nonincreasing). `VgN`, `KgN` are Algorithm 1 (16)–(22). -/
theorem proposition_4 (M : Model) (hM : M.Standing) (obj : Objective) :
    ∀ g : ℝ, 0 ≤ g → ∀ N : ℕ, 1 ≤ N →
      ConcaveOn ℝ (Icc 0 (wbar M + M.C)) (VgN M obj g N) ∧
      AntitoneOn (KgN M obj g N) (Icc 0 (wbar M + M.C)) := by sorry

end WaitTimePricing.Existence
