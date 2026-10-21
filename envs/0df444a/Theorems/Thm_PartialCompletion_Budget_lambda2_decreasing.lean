-- Prove2me | Theorems.Thm_PartialCompletion_Budget_lambda2_decreasing
-- name    : PartialCompletion.Budget.lambda2_decreasing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:47.13929+00:00
-- url     : https://prove2.me/theorems/faa9b1da-db29-4c04-aa24-b533a869f938
-- title:
--   Proof of Proposition 3, Online Appendix p. 3 — Λ₂ decreases in variety
-- statement:
--   For a fixed nonnegative budget $B$, define the second derivative-sign factor on the binding-budget curve by
--
--   $$
--   \Lambda_2(B,n)=\frac{\theta[g(n)+ng'(n)]}{4n^2g'(n)}-2\beta\left(1-\frac{B}{g(n)}\right).
--   $$
--
--   The appendix asserts that this function is strictly decreasing for $n\ge1$. This gives at most one stationary variety in the middle-budget regime.
--
--   **Formalization Note** Strictness at $B=0$ comes from the first summand and $\theta>0$. The appendix's printed $g''_2(n)$ in a derivative display is treated as the apparent typo $g''(n)$.
-- source:
--   Zhang, Atasu & Ramachandran, Partial Completion as a Nonprofit Strategy, SSRN 3684891, Online Appendix p. 3 (PDF 36), proof of Proposition 3, Case 2

import Mathlib
import Definitions.Def_PartialCompletion_Budget_Model

namespace PartialCompletion.Budget

theorem lambda2_decreasing (M : Model) (hM : M.Standing)
    (B : ℝ) (hB : 0 ≤ B) :
    StrictAntiOn (Λ2 M B) (Set.Ici 1) := by sorry

end PartialCompletion.Budget
