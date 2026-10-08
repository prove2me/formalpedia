-- Prove2me | Theorems.Thm_PoissonDepTrials_MixInv_lemma_3_5
-- name    : PoissonDepTrials.MixInv.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:54:11.825303+00:00
-- url     : https://prove2.me/theorems/530f1a82-b67a-4d07-893c-cd3a5457db68
-- title:
--   Lemma 3.5, p. 537 — |ΔS_λh(w)| ≤ λ^{−1}‖h‖{2 + 4|w − λ| min(λ^{−1/2}, 1)} for w ≥ 1
-- statement:
--   Let $\lambda>0$ and let $h$ be a bounded real function with $|h|\le M$. For every $w\ge1$,
--   $$|\Delta S_\lambda h(w)|\le\lambda^{-1}M\bigl\{2+4|w-\lambda|\min(\lambda^{-1/2},1)\bigr\}.$$
--   Unlike Lemma 3.4, this bound decays like $\lambda^{-1}$ when $w$ is close to $\lambda$; it is the source of the order-$\lambda^{-1}$ rate in Theorem 4.2.
--
--   **Formalization Note** The sup norm $\|h\|$ is replaced by any bound $M$ with $|h(k)|\le M$ for all $k$, which is equivalent since $\|h\|$ is the least such $M$; $\|S_\lambda h\|$ is a supremum over $w\ge1$, the domain of $S_\lambda h$, so the statement quantifies over $w\ge 1$. The paper's §3 divides by $\lambda$, so $\lambda>0$ is an implicit hypothesis and is stated.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 537, Lemma 3.5, (3.5)

import Mathlib
import Definitions.Def_PoissonDepTrials_MixInv_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixInv

theorem lemma_3_5 (lam : ℝ) (hlam : 0 < lam) (h : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |h k| ≤ M) :
    ∀ w : ℕ, 1 ≤ w → |delta (stein lam h) w| ≤
      lam⁻¹ * M * (2 + 4 * |(w : ℝ) - lam| * min (1 / Real.sqrt lam) 1) := by sorry

end PoissonDepTrials.MixInv
