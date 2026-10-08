-- Prove2me | Theorems.Thm_PoissonDepTrials_SecondOrder_lemma_3_5
-- name    : PoissonDepTrials.SecondOrder.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:51:26.713148+00:00
-- url     : https://prove2.me/theorems/0afe20d9-6371-49ba-8565-da002af70362
-- title:
--   Lemma 3.5, p. 537 — |ΔS_λh(w)| ≤ λ^{−1}‖h‖{2 + 4|w − λ| min(λ^{−½}, 1)} for w ≥ 1
-- statement:
--   Let $\lambda>0$ and $|h(k)|\le M$ for all $k$. Then for every $w\ge1$,
--   $$|\Delta S_\lambda h(w)|\le\lambda^{-1}M\bigl\{2+4|w-\lambda|\min(\lambda^{-1/2},1)\bigr\}.$$
--
--   Unlike the uniform bound of Lemma 3.4, this bound gains a factor $\lambda^{-1}$ near $w=\lambda$, which is what makes the error of the second-order expansion of order $\lambda^{-1}\sum p_i^3$. Since $U_\lambda h(w)=\Delta S_\lambda h(w+1)$, it bounds $U_\lambda h$ pointwise.
--
--   **Formalization Note** $\|h\|$ is replaced by a bound $M$ on $|h|$; $\lambda>0$ is implicit on the page.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 537, Lemma 3.5, (3.5)

import Mathlib
import Definitions.Def_PoissonDepTrials_SecondOrder_Setting

open MeasureTheory ProbabilityTheory Finset

namespace PoissonDepTrials.SecondOrder

/-- Lemma 3.5, (3.5), p. 537: for `w ≥ 1`,
`|ΔS_λh(w)| ≤ λ^{−1}‖h‖{2 + 4|w − λ| min(λ^{−1/2}, 1)}`. -/
theorem lemma_3_5 (lam : ℝ) (hlam : 0 < lam) (h : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |h k| ≤ M) :
    ∀ w : ℕ, 1 ≤ w → |delta (stein lam h) w| ≤
      lam⁻¹ * M * (2 + 4 * |(w : ℝ) - lam| * min (1 / Real.sqrt lam) 1) := by sorry

end PoissonDepTrials.SecondOrder
