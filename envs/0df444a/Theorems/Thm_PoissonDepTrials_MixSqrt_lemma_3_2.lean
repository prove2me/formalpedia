-- Prove2me | Theorems.Thm_PoissonDepTrials_MixSqrt_lemma_3_2
-- name    : PoissonDepTrials.MixSqrt.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:37:58.943535+00:00
-- url     : https://prove2.me/theorems/3bdd3c26-9ea4-4b69-8e50-5ceab2cc71ad
-- title:
--   Lemma 3.2, p. 537 — (w − 1)! λ^{−w} Σ_{k≥w} λ^k/k! ≤ 2w^{−1/2} for 0 < λ ≤ w, w ≥ 1
-- statement:
--   Let $w\ge1$ be an integer and $0<\lambda\le w$. Then
--   $$(w-1)!\,\lambda^{-w}\sum_{k=w}^\infty\frac{\lambda^k}{k!}\le 2w^{-1/2}.$$
--
--   Together with the second line of (2.5) this bounds $|S_\lambda h(w)|$ in the regime $\lambda\le w$ (Lemma 3.3).
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 537, Lemma 3.2, (3.2)

import Mathlib
import Definitions.Def_PoissonDepTrials_MixSqrt_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixSqrt

/-- Chen (1975), Lemma 3.2, p. 537, (3.2): for `0 < λ ≤ w` and `w ≥ 1`,
`(w − 1)! λ^{−w} Σ_{k=w}^∞ λ^k / k! ≤ 2w^{−1/2}`. -/
theorem lemma_3_2 (lam : ℝ) (hlam : 0 < lam) (w : ℕ) (hw : 1 ≤ w) (hlw : lam ≤ w) :
    ((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ * ∑' k : ℕ, lam ^ (k + w) / ((k + w).factorial : ℝ)
      ≤ 2 / Real.sqrt w := by sorry

end PoissonDepTrials.MixSqrt
