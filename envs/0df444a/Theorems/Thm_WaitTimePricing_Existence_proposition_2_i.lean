-- Prove2me | Theorems.Thm_WaitTimePricing_Existence_proposition_2_i
-- name    : WaitTimePricing.Existence.proposition_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T11:25:45.676792+00:00
-- url     : https://prove2.me/theorems/5a0f2580-8bbf-489f-b7b9-4a92bf48d973
-- title:
--   Proposition 2(i) — a unique positive $\bar w$ with $U(C)=c(\bar w)$
-- statement:
--   Under Assumption 1 there exists a unique positive threshold $\bar w$ such that
--   $$U(C)=c(\bar w).$$
--
--   No price induces a customer facing a wait time above $\bar w$ to join, so the wait time never exceeds $\bar w$; $\bar w$ is the right end of the domain of the optimality equations.
--
--   **Formalization Note** $\bar w$ is defined as the supremum of the positive solutions; the statement asserts that it is positive, solves the equation, and is the only positive solution.
-- source:
--   Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 9, Proposition 2(i), (7)

import Mathlib
import Definitions.Def_WaitTimePricing_Existence_Setting

namespace WaitTimePricing.Existence

open Set Filter

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 9, Proposition 2(i), (7).

Under Assumption 1 there is a unique positive threshold `w̄` with `U(C) = c(w̄)`.

**Formalization Note.** `wbar M` is defined by its characterizing set (`sup {w > 0 | U(C) = c(w)}`);
the theorem asserts that it is positive, solves (7), and is the only positive solution. -/
theorem proposition_2_i (M : Model) (hM : M.Standing) :
    0 < wbar M ∧ M.U M.C = M.c (wbar M) ∧
    ∀ w : ℝ, 0 < w → M.U M.C = M.c w → w = wbar M := by sorry

end WaitTimePricing.Existence
