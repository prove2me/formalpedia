-- Prove2me | Theorems.Thm_WaitTimePricing_Existence_lemma_3
-- name    : WaitTimePricing.Existence.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T11:26:27.385781+00:00
-- url     : https://prove2.me/theorems/60fccdc0-9933-4daa-9566-ba91815fbe2a
-- title:
--   Lemma 3 — $K^{g_1}_N\ge K^{g_2}_N$ for $0\le g_1<g_2$
-- statement:
--   For every $N\ge1$ and all $g_1,g_2$ with $0\le g_1<g_2$,
--   $$K^{g_1}_N(w)\ge K^{g_2}_N(w)\qquad\text{for all } w\in[0,\bar w+C].$$
--
--   Raising the guessed rate $g$ lowers the slope adjustment; together with Lemma 2 this is what lets the shooting value $g_N$ be tuned.
--
--   **Formalization Note** "For any given $N$" means $N\ge1$.
-- source:
--   Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 15, Lemma 3

import Mathlib
import Definitions.Def_WaitTimePricing_Existence_Setting
import Definitions.Def_WaitTimePricing_Existence_Algorithm1

namespace WaitTimePricing.Existence

open Set Filter

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 15, Lemma 3.

For any given `N`, and `g₁`, `g₂` with `0 ≤ g₁ < g₂`, `K^{g₁}_N(w) ≥ K^{g₂}_N(w)` for all
`w ∈ [0, w̄ + C]`.

**Formalization Note.** `N ≥ 1` (`ε_N = w̄/N`). -/
theorem lemma_3 (M : Model) (hM : M.Standing) (obj : Objective) :
    ∀ N : ℕ, 1 ≤ N → ∀ g₁ g₂ : ℝ, 0 ≤ g₁ → g₁ < g₂ → ∀ w ∈ Icc 0 (wbar M + M.C),
      KgN M obj g₂ N w ≤ KgN M obj g₁ N w := by sorry

end WaitTimePricing.Existence
