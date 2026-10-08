-- Prove2me | Theorems.Thm_PoissonDepTrials_SecondOrder_lemma_3_2
-- name    : PoissonDepTrials.SecondOrder.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:38:58.097837+00:00
-- url     : https://prove2.me/theorems/8e169b66-463f-432d-afdd-b56ebe150a9a
-- title:
--   Lemma 3.2, p. 537 — (w − 1)! λ^{−w} Σ_{k≥w} λ^k/k! ≤ 2w^{−½} for 0 < λ ≤ w, w ≥ 1
-- statement:
--   For $0<\lambda\le w$ and an integer $w\ge1$,
--   $$(w-1)!\,\lambda^{-w}\sum_{k=w}^\infty\frac{\lambda^k}{k!}\le 2w^{-1/2}.$$
--
--   This bounds the tail representation of $S_\lambda h$ in (2.5) in the range $w\ge\lambda$; it is the other half of the proof of Lemma 3.3.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 537, Lemma 3.2, (3.2)

import Mathlib
import Definitions.Def_PoissonDepTrials_SecondOrder_Setting

open MeasureTheory ProbabilityTheory Finset

namespace PoissonDepTrials.SecondOrder

/-- Lemma 3.2, (3.2), p. 537: for `0 < λ ≤ w` and `w ≥ 1`,
`(w − 1)! λ^{−w} Σ_{k=w}^∞ λ^k/k! ≤ 2w^{−1/2}`. -/
theorem lemma_3_2 (lam : ℝ) (hlam : 0 < lam) (w : ℕ) (hw : 1 ≤ w) (hlw : lam ≤ w) :
    ((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ * ∑' k : ℕ, lam ^ (k + w) / ((k + w).factorial : ℝ)
      ≤ 2 / Real.sqrt w := by sorry

end PoissonDepTrials.SecondOrder
