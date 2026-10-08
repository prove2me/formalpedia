-- Prove2me | Theorems.Thm_PoissonDepTrials_MixInv_lemma_3_3
-- name    : PoissonDepTrials.MixInv.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:54:04.272496+00:00
-- url     : https://prove2.me/theorems/39a9e17c-d4fb-411a-871e-7fa13305c581
-- title:
--   Lemma 3.3, p. 537 — ‖S_λh‖ ≤ 4‖h‖ min(λ^{−1/2}, 1)
-- statement:
--   Let $\lambda>0$ and let $h$ be a bounded real function on the nonnegative integers with $|h|\le M$. Then for every $w\ge1$,
--   $$|S_\lambda h(w)|\le 4M\min(\lambda^{-1/2},1).$$
--   This is the paper's (3.3), $\|S_\lambda h\|\le4\|h\|\min(\lambda^{-1/2},1)$; it bounds the middle error term of (2.6) through Lemma 4.6.
--
--   **Formalization Note** The sup norm $\|h\|$ is replaced by any bound $M$ with $|h(k)|\le M$ for all $k$, which is equivalent since $\|h\|$ is the least such $M$; $\|S_\lambda h\|$ is a supremum over $w\ge1$, the domain of $S_\lambda h$, so the statement quantifies over $w\ge 1$. The paper's §3 divides by $\lambda$, so $\lambda>0$ is an implicit hypothesis and is stated.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 537, Lemma 3.3, (3.3)

import Mathlib
import Definitions.Def_PoissonDepTrials_MixInv_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixInv

theorem lemma_3_3 (lam : ℝ) (hlam : 0 < lam) (h : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |h k| ≤ M) :
    ∀ w : ℕ, 1 ≤ w → |stein lam h w| ≤ 4 * M * min (1 / Real.sqrt lam) 1 := by sorry

end PoissonDepTrials.MixInv
