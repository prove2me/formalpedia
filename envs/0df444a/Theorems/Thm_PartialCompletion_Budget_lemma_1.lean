-- Prove2me | Theorems.Thm_PartialCompletion_Budget_lemma_1
-- name    : PartialCompletion.Budget.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:40.880422+00:00
-- url     : https://prove2.me/theorems/cfe5f3ae-b764-451f-9b90-094157b39e9f
-- title:
--   Lemma 1, p. 12 — unconstrained optimal variety and completion
-- statement:
--   Let the nonprofit choose real variety $n\ge1$ and completion $\alpha\in[0,1]$ under the stated quadratic effort and increasing convex variety cost. Write $n^*_{NB}$ for $1$ when $\theta/4\le g'(1)$, and otherwise for the variety above $1$ solving $\theta/(4n^2)=g'(n)$. Set $\alpha^*_{NB}=\max\{1-[\theta/(4n^*_{NB})+g(n^*_{NB})]/(2\beta),0\}$. Then $(n^*_{NB},\alpha^*_{NB})$ is feasible without a budget bound and
--
--   $$
--   W(n,\alpha)\le W(n^*_{NB},\alpha^*_{NB})\qquad(n\ge1,\ 0\le\alpha\le1).
--   $$
--
--   The optimum also satisfies $\alpha^*_{NB}\ge1-1/(2\beta)$. This result supplies the ample-budget pair used by the budget-regime theorem.
--
--   **Formalization Note** The variety is supplied by its unique characterization; its existence is not assumed for arbitrary model data. The standing worthwhile-provision condition is included.
-- source:
--   Zhang, Atasu & Ramachandran, Partial Completion as a Nonprofit Strategy, SSRN 3684891, p. 12, Lemma 1; proof in Online Appendix p. 1 (PDF 34)

import Mathlib
import Definitions.Def_PartialCompletion_Budget_Model

namespace PartialCompletion.Budget

theorem lemma_1 (M : Model) (hM : M.Standing) (nNB : ℝ)
    (hNB : IsNNB M nNB) :
    (nNB, alphaAmple M nNB) ∈ Unconstrained ∧
    IsMaxOn (W M) Unconstrained (nNB, alphaAmple M nNB) ∧
    1 - 1 / (2 * M.β) ≤ alphaAmple M nNB := by sorry

end PartialCompletion.Budget
