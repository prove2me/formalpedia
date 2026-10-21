-- Prove2me | Theorems.Thm_PartialCompletion_Budget_case1_global_optimal
-- name    : PartialCompletion.Budget.case1_global_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:39.483976+00:00
-- url     : https://prove2.me/theorems/716bfdd1-4bf7-4273-b846-9fa95ea3a240
-- title:
--   Proof of Proposition 3, Online Appendix p. 2 — global small-budget optimum
-- statement:
--   Let $n_0$ be the appendix's small-budget variety: $n_0=1$ if $\Lambda_1(1)\le0$, or $n_0>1$ and $\Lambda_1(n_0)=0$ otherwise. For every nonnegative budget below $(1-1/(2\beta))g(n_0)$, the feasible pair
--
--   $$
--   \left(n_0,\frac{B}{g(n_0)}\right)
--   $$
--
--   maximizes the total net benefit among all feasible variety and completion choices. This is the global small-budget claim, including choices on either side of the beneficiary-effort switch.
--
--   **Formalization Note** When $\beta\le1/2$ the stated budget interval is empty, as in the paper's Case 1 condition.
-- source:
--   Zhang, Atasu & Ramachandran, Partial Completion as a Nonprofit Strategy, SSRN 3684891, Online Appendix p. 2 (PDF 35), proof of Proposition 3, Case 1, summary

import Mathlib
import Definitions.Def_PartialCompletion_Budget_Model

namespace PartialCompletion.Budget

theorem case1_global_optimal (M : Model) (hM : M.Standing)
    (n0 : ℝ) (hn0 : IsN0 M n0) (B : ℝ) (hB : 0 ≤ B)
    (hsmall : B < (1 - 1 / (2 * M.β)) * M.g n0) :
    IsOptimal M B (n0, B / M.g n0) := by sorry

end PartialCompletion.Budget
