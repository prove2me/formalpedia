-- Prove2me | Theorems.Thm_PartialCompletion_Budget_proposition_3
-- name    : PartialCompletion.Budget.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:45.682005+00:00
-- url     : https://prove2.me/theorems/31fcb606-d31c-46de-b81f-51e4a766aacd
-- title:
--   Proposition 3, p. 13 — three optimal budget regimes and monotonic choices
-- statement:
--   Under the quadratic partial-completion model, let $(n^*_{NB},\alpha^*_{NB})$ be the unconstrained optimum and $B_2=\alpha^*_{NB}g(n^*_{NB})$. There exist $0\le B_1\le B_2$, a variety $n_0\ge1$, and a middle-regime variety choice $n_1(B)$ such that, for every nonnegative budget, an optimal feasible pair is
--
--   $$
--   (n^*,\alpha^*)=\begin{cases}
--   (n_0,B/g(n_0)),&B<B_1,\\
--   (n_1(B),B/g(n_1(B))),&B_1\le B<B_2,\\
--   (n^*_{NB},\alpha^*_{NB}),&B\ge B_2.
--   \end{cases}
--   $$
--
--   Both $n_1(B)$ and $B/g(n_1(B))$ are nondecreasing on the middle interval. The small-budget variety is pinned down by $\Lambda_1$: it is $1$ if $\Lambda_1(1)\le0$ or a root above $1$ otherwise; moreover $B_1\ge(1-1/(2\beta))g(n_0)$. The result describes how budget first supports completion, then jointly supports variety and completion, before reaching the unconstrained optimum.
--
--   **Formalization Note** The paper uses “increasing” weakly. Optimality means membership and maximality; uniqueness is not asserted when zero completion makes varieties interchangeable. The appendix's uncapped candidate for $B_1$ can exceed $B_2$ when $n^*_{NB}=1$, so the proposition's existential threshold is retained. The added domains $\theta>0$, $\beta>0$, and $B\ge0$ are explicit.
-- source:
--   Zhang, Atasu & Ramachandran, Partial Completion as a Nonprofit Strategy, SSRN 3684891, p. 13, Proposition 3; proof in Online Appendix pp. 2–3 (PDF 35–36)

import Mathlib
import Definitions.Def_PartialCompletion_Budget_Model

namespace PartialCompletion.Budget

theorem proposition_3 (M : Model) (hM : M.Standing)
    (nNB : ℝ) (hNB : IsNNB M nNB) :
    ∃ B1 n0 : ℝ, ∃ n1 : ℝ → ℝ,
      0 ≤ B1 ∧
      B1 ≤ alphaAmple M nNB * M.g nNB ∧
      IsN0 M n0 ∧
      (1 - 1 / (2 * M.β)) * M.g n0 ≤ B1 ∧
      (∀ B : ℝ, 0 ≤ B → B < B1 →
        IsOptimal M B (n0, B / M.g n0)) ∧
      (∀ B : ℝ, 0 ≤ B → B1 ≤ B →
        B < alphaAmple M nNB * M.g nNB →
        IsOptimal M B (n1 B, B / M.g (n1 B))) ∧
      MonotoneOn n1
        (Set.Ico B1 (alphaAmple M nNB * M.g nNB) ∩ Set.Ici 0) ∧
      MonotoneOn (fun B : ℝ => B / M.g (n1 B))
        (Set.Ico B1 (alphaAmple M nNB * M.g nNB) ∩ Set.Ici 0) ∧
      (∀ B : ℝ, alphaAmple M nNB * M.g nNB ≤ B →
        IsOptimal M B (nNB, alphaAmple M nNB)) := by sorry

end PartialCompletion.Budget
