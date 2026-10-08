-- Prove2me | Theorems.Thm_PoissonDepTrials_SecondOrder_lemma_5_4
-- name    : PoissonDepTrials.SecondOrder.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:52:19.430431+00:00
-- url     : https://prove2.me/theorems/a018e85f-daff-4d2b-ae5c-1abe55547688
-- title:
--   Lemma 5.4, p. 543 — |S_bU_λh(w)| ≤ 4λ^{−1}‖h‖[(2 + 4|1 + b − λ|) min(b^{−½}, 1) + 3 min(λ^{−½}, 1)] for w ≥ 1
-- statement:
--   Let $\lambda>0$, $b>0$ and $|h(k)|\le M$ for all $k$. Let $S_bU_\lambda h$ be the Stein solution with parameter $b$ applied to the function $U_\lambda h$. Then for every $w\ge1$,
--   $$\bigl|S_bU_\lambda h(w)\bigr|\le4\lambda^{-1}M\Bigl[(2+4|1+b-\lambda|)\min(b^{-1/2},1)+3\min(\lambda^{-1/2},1)\Bigr].$$
--
--   This is the analogue of Lemma 3.3 for the iterated operator and an input of Lemma 5.5.
--
--   **Formalization Note** $b>0$ is the standing range of §5; $\lambda>0$ is implicit. $\|h\|$ is replaced by a bound $M$.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 543, Lemma 5.4, (5.4)

import Mathlib
import Definitions.Def_PoissonDepTrials_SecondOrder_Setting

open MeasureTheory ProbabilityTheory Finset

namespace PoissonDepTrials.SecondOrder

/-- Lemma 5.4, (5.4), p. 543: for `w ≥ 1`,
`|S_bU_λh(w)| ≤ 4λ^{−1}‖h‖[(2 + 4|1 + b − λ|) min(b^{−1/2}, 1) + 3 min(λ^{−1/2}, 1)]`. -/
theorem lemma_5_4 (lam : ℝ) (hlam : 0 < lam) (b : ℝ) (hb : 0 < b) (h : ℕ → ℝ) (M : ℝ)
    (hM : ∀ k, |h k| ≤ M) :
    ∀ w : ℕ, 1 ≤ w → |stein b (stU lam h) w| ≤
      4 * lam⁻¹ * M * ((2 + 4 * |1 + b - lam|) * min (1 / Real.sqrt b) 1 +
        3 * min (1 / Real.sqrt lam) 1) := by sorry

end PoissonDepTrials.SecondOrder
