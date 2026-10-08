-- Prove2me | Theorems.Thm_PoissonDepTrials_SecondOrder_lemma_3_3
-- name    : PoissonDepTrials.SecondOrder.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:51:17.468141+00:00
-- url     : https://prove2.me/theorems/a76e7262-17c0-4f7a-86b8-8716a602ac86
-- title:
--   Lemma 3.3, p. 537 — ‖S_λh‖ ≤ 4‖h‖ min(λ^{−½}, 1)
-- statement:
--   Let $\lambda>0$ and let $h$ be a function on the nonnegative integers with $|h(k)|\le M$ for all $k$. Then for every $w\ge1$,
--   $$|S_\lambda h(w)|\le 4M\min(\lambda^{-1/2},1).$$
--
--   This is the basic uniform bound on the Stein solution; it enters Lemma 3.5 and through it every bound of §5.
--
--   **Formalization Note** The page's $\|S_\lambda h\|\le4\|h\|\min(\lambda^{-1/2},1)$ is a sup over the domain $w\ge1$ of $S_\lambda h$, and $\|h\|$ is the sup norm; both are expressed with an arbitrary bound $M$ on $|h|$, which is equivalent. $\lambda>0$ is implicit on the page.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 537, Lemma 3.3, (3.3)

import Mathlib
import Definitions.Def_PoissonDepTrials_SecondOrder_Setting

open MeasureTheory ProbabilityTheory Finset

namespace PoissonDepTrials.SecondOrder

/-- Lemma 3.3, (3.3), p. 537: `‖S_λh‖ ≤ 4‖h‖ min(λ^{−1/2}, 1)`, the norm of `S_λh` taken over
its domain `w ≥ 1` and `‖h‖` replaced by any bound `M` on `|h|`. -/
theorem lemma_3_3 (lam : ℝ) (hlam : 0 < lam) (h : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |h k| ≤ M) :
    ∀ w : ℕ, 1 ≤ w → |stein lam h w| ≤ 4 * M * min (1 / Real.sqrt lam) 1 := by sorry

end PoissonDepTrials.SecondOrder
