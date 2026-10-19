-- Prove2me | Theorems.Thm_WaitTimePricing_Existence_proposition_5
-- name    : WaitTimePricing.Existence.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T11:26:44.648091+00:00
-- url     : https://prove2.me/theorems/5f636e7a-068d-4946-b0b7-df7c59e702b4
-- title:
--   Proposition 5 — $g_{2^j}$ is nondecreasing, bounded by $U'(0)$, and converges to $\bar g$
-- statement:
--   Let $g_N$ be the shooting value (23). For $j=1,2,\dots$:
--
--   1. $0\le g_{2^j}\le U'(0)$;
--   2. $g_{2^j}\le g_{2^{j+1}}$;
--   3. consequently the limit
--   $$\bar g=\lim_{j\to\infty}g_{2^j}$$
--   exists.
--
--   $\bar g$ is the candidate optimal long-run average rate.
--
--   **Formalization Note** "Monotonically increasing" is the weak inequality. The bound $0\le g_{2^j}$ is from the paper's proof. $\bar g$ is defined as a limit with a default value; the third item asserts that the sequence actually converges to it.
-- source:
--   Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 16, Proposition 5, (24)

import Mathlib
import Definitions.Def_WaitTimePricing_Existence_Setting
import Definitions.Def_WaitTimePricing_Existence_Algorithm1

namespace WaitTimePricing.Existence

open Set Filter

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 16, Proposition 5, (24).

The sequence `g_{2^j}`, `j = 1, 2, …`, defined by (23), is monotonically increasing in `j` and
bounded above by `U′(0)`; therefore the limit `ḡ := lim_{j→∞} g_{2^j}` exists.

**Formalization Note.** "Monotonically increasing" is the weak inequality `g_{2^j} ≤ g_{2^{j+1}}`
(the proof shows `g_{2j} ≥ g_j`). The conjunct `0 ≤ g_{2^j}` is from the proof (p. 37). `gbar` is a
`limUnder`; the last conjunct asserts that the sequence actually converges to it. -/
theorem proposition_5 (M : Model) (hM : M.Standing) (obj : Objective) :
    (∀ j : ℕ, 1 ≤ j → 0 ≤ gN M obj (2 ^ j)) ∧
    (∀ j : ℕ, 1 ≤ j → gN M obj (2 ^ j) ≤ gN M obj (2 ^ (j + 1))) ∧
    (∀ j : ℕ, 1 ≤ j → gN M obj (2 ^ j) ≤ deriv M.U 0) ∧
    Tendsto (fun j : ℕ => gN M obj (2 ^ j)) atTop (nhds (gbar M obj)) := by sorry

end WaitTimePricing.Existence
