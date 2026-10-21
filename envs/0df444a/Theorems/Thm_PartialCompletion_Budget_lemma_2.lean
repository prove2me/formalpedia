-- Prove2me | Theorems.Thm_PartialCompletion_Budget_lemma_2
-- name    : PartialCompletion.Budget.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:41.588984+00:00
-- url     : https://prove2.me/theorems/c1651b9a-368e-40e9-81bc-d13169ed6d3f
-- title:
--   Lemma 2, p. 13 — every optimum below B₂ exhausts the budget
-- statement:
--   Let $(n^*_{NB},\alpha^*_{NB})$ be the unconstrained optimum of the quadratic partial-completion model and put $B_2=\alpha^*_{NB}g(n^*_{NB})$. For a nonnegative budget below $B_2$, every feasible maximizer $(n^*,\alpha^*)$ of the total net benefit satisfies
--
--   $$
--   0\le B<B_2\quad\Longrightarrow\quad\alpha^*g(n^*)=B.
--   $$
--
--   Thus the budget constraint binds throughout the part of the allocation problem below the ample-budget threshold.
--
--   **Formalization Note** An optimal point is explicitly a member of the budget feasible set, and the budget is nonnegative.
-- source:
--   Zhang, Atasu & Ramachandran, Partial Completion as a Nonprofit Strategy, SSRN 3684891, p. 13, Lemma 2; proof in Online Appendix pp. 1–2 (PDF 34–35)

import Mathlib
import Definitions.Def_PartialCompletion_Budget_Model

namespace PartialCompletion.Budget

theorem lemma_2 (M : Model) (hM : M.Standing) (nNB : ℝ)
    (hNB : IsNNB M nNB) (B : ℝ) (hB : 0 ≤ B)
    (hbelow : B < alphaAmple M nNB * M.g nNB) :
    ∀ p : ℝ × ℝ, IsOptimal M B p → p.2 * M.g p.1 = B := by sorry

end PartialCompletion.Budget
