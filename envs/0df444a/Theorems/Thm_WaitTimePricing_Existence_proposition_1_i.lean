-- Prove2me | Theorems.Thm_WaitTimePricing_Existence_proposition_1_i
-- name    : WaitTimePricing.Existence.proposition_1_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T11:25:45.47123+00:00
-- url     : https://prove2.me/theorems/cc5e8dde-6913-4a40-a5a3-31e4db7ffb13
-- title:
--   Proposition 1(i) — a unique positive $\hat w$ with $U(C)-U'(C)C-c(\hat w)=0$
-- statement:
--   Under Assumption 1 there exists a unique positive threshold $\hat w$ such that
--   $$U(C)-U'(C)\,C-c(\hat w)=0.$$
--
--   Beyond $\hat w$ the firm can no longer induce a customer to join with a price $p=U'(t)\in[U'(C),U'(0)]$; it must offer a price below $U'(C)$ and the maximum service time $C$.
--
--   **Formalization Note** $\hat w$ is defined as the supremum of the positive solutions of the equation; the statement asserts that it is positive, solves the equation, and is the only positive solution.
-- source:
--   Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 8, Proposition 1(i), (3)

import Mathlib
import Definitions.Def_WaitTimePricing_Existence_Setting

namespace WaitTimePricing.Existence

open Set Filter

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 8, Proposition 1(i), (3).

Under Assumption 1 there is a unique positive threshold `ŵ` with `U(C) − U′(C)C − c(ŵ) = 0`.

**Formalization Note.** `what M` is defined by its characterizing set
(`sup {w > 0 | U(C) − U′(C)C − c(w) = 0}`); the theorem asserts that it is positive, solves (3), and
is the only positive solution. Standing assumptions: see `Model.Standing`. -/
theorem proposition_1_i (M : Model) (hM : M.Standing) :
    0 < what M ∧
    M.U M.C - deriv M.U M.C * M.C - M.c (what M) = 0 ∧
    ∀ w : ℝ, 0 < w → M.U M.C - deriv M.U M.C * M.C - M.c w = 0 → w = what M := by sorry

end WaitTimePricing.Existence
