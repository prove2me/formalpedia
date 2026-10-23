-- Prove2me | Theorems.Thm_WaitTimePricing_Existence_lemma_2
-- name    : WaitTimePricing.Existence.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T11:26:38.713765+00:00
-- url     : https://prove2.me/theorems/3660cb96-0863-4983-bba4-582143ba34a7
-- title:
--   Lemma 2 — grid refinement: $V^g_j\ge V^g_{2j}$ and $K^g_j\le K^g_{2j}$
-- statement:
--   For every $g\ge 0$ and every positive integer $j$,
--   $$V^g_j(w)\ge V^g_{2j}(w)\quad\text{and}\quad K^g_j(w)\le K^g_{2j}(w)\qquad\text{for all } w\in[0,\bar w+C].$$
--
--   Doubling the number of grid cells raises the slope adjustment and lowers the approximate value function.
-- source:
--   Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 15, Lemma 2

import Mathlib
import Definitions.Def_WaitTimePricing_Existence_Setting
import Definitions.Def_WaitTimePricing_Existence_Algorithm1

namespace WaitTimePricing.Existence

open Set Filter

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 15, Lemma 2.

Given `g ≥ 0` and any positive integer `j`, `V^g_j(w) ≥ V^g_{2j}(w)` and `K^g_j(w) ≤ K^g_{2j}(w)` for
all `w ∈ [0, w̄ + C]`. -/
theorem lemma_2 (M : Model) (hM : M.Standing) (obj : Objective) :
    ∀ g : ℝ, 0 ≤ g → ∀ j : ℕ, 1 ≤ j → ∀ w ∈ Icc 0 (wbar M + M.C),
      VgN M obj g (2 * j) w ≤ VgN M obj g j w ∧ KgN M obj g j w ≤ KgN M obj g (2 * j) w := by sorry

end WaitTimePricing.Existence
