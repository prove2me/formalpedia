-- Prove2me | Theorems.Thm_PartialCompletion_Budget_lambda2_roots_increasing
-- name    : PartialCompletion.Budget.lambda2_roots_increasing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:44.69458+00:00
-- url     : https://prove2.me/theorems/e41daa78-8d20-4131-afae-86570713c966
-- title:
--   Proof of Proposition 3, Online Appendix p. 3 — middle-regime choices increase
-- statement:
--   For budgets $0\le B\le B'$ and varieties $n,n'\ge1$ satisfying $\Lambda_2(B,n)=0$ and $\Lambda_2(B',n')=0$, the appendix's middle-regime comparative static is
--
--   $$
--   n\le n',\qquad \frac{B}{g(n)}\le\frac{B'}{g(n')}.
--   $$
--
--   Thus any existing roots selected along this branch have nondecreasing variety and completion as the budget rises. This is the monotonicity needed in Proposition 3.
--
--   **Formalization Note** The theorem is conditional on roots existing at both budgets; it does not claim that a root exists for every nonnegative budget.
-- source:
--   Zhang, Atasu & Ramachandran, Partial Completion as a Nonprofit Strategy, SSRN 3684891, Online Appendix p. 3 (PDF 36), proof of Proposition 3, Case 2, monotonicity paragraph

import Mathlib
import Definitions.Def_PartialCompletion_Budget_Model

namespace PartialCompletion.Budget

theorem lambda2_roots_increasing (M : Model) (hM : M.Standing)
    (B B' n n' : ℝ) (hB : 0 ≤ B) (hBB' : B ≤ B')
    (hn : 1 ≤ n) (hn' : 1 ≤ n')
    (hroot : Λ2 M B n = 0) (hroot' : Λ2 M B' n' = 0) :
    n ≤ n' ∧ B / M.g n ≤ B' / M.g n' := by sorry

end PartialCompletion.Budget
