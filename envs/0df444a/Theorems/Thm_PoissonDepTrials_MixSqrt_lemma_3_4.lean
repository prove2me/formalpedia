-- Prove2me | Theorems.Thm_PoissonDepTrials_MixSqrt_lemma_3_4
-- name    : PoissonDepTrials.MixSqrt.lemma_3_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:37:56.276545+00:00
-- url     : https://prove2.me/theorems/a03f915d-1804-4388-b567-c161998719e4
-- title:
--   Lemma 3.4, p. 537 — ‖ΔS_λh‖ ≤ 6‖h‖ min(λ^{−1/2}, 1)
-- statement:
--   Let $\lambda>0$ and let $h$ be a real function on the nonnegative integers with $|h(k)|\le M$ for all $k$. Then for every $w\ge1$,
--   $$|\Delta S_\lambda h(w)|=|S_\lambda h(w+1)-S_\lambda h(w)|\le 6M\min(\lambda^{-1/2},1).$$
--   Equivalently, $\|\Delta S_\lambda h\|\le6\|h\|\min(\lambda^{-1/2},1)$.
--
--   This bounds the first and third error terms of (2.6) and produces the constant $6$ of Theorem 4.1.
--
--   **Formalization Note** $\|h\|$ is an arbitrary bound $M$ on $|h|$; the supremum defining $\|\Delta S_\lambda h\|$ is over $w\ge1$. The hypothesis $\lambda>0$ is implicit on the page.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 537, Lemma 3.4, (3.4) (proved with (3.6), (3.7) and Lemma 3.3)

import Mathlib
import Definitions.Def_PoissonDepTrials_MixSqrt_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixSqrt

/-- Chen (1975), Lemma 3.4, p. 537, (3.4): `‖ΔS_λh‖ ≤ 6‖h‖ min(λ^{−1/2}, 1)`, with `‖h‖` given
as any bound `M` on `|h|` and the supremum over `w ≥ 1`. -/
theorem lemma_3_4 (lam : ℝ) (hlam : 0 < lam) (h : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |h k| ≤ M) :
    ∀ w : ℕ, 1 ≤ w → |delta (stein lam h) w| ≤ 6 * M * min (1 / Real.sqrt lam) 1 := by sorry

end PoissonDepTrials.MixSqrt
