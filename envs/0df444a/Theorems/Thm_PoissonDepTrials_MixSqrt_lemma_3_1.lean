-- Prove2me | Theorems.Thm_PoissonDepTrials_MixSqrt_lemma_3_1
-- name    : PoissonDepTrials.MixSqrt.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:37:52.203647+00:00
-- url     : https://prove2.me/theorems/c2d1cb16-5ce9-4707-b4f7-5301284f43a9
-- title:
--   Lemma 3.1, p. 536 — (w − 1)! λ^{−w} Σ_{k=0}^{w−1} λ^k/k! ≤ 2λ^{−1/2} for λ ≥ w ≥ 1
-- statement:
--   Let $w\ge1$ be an integer and $\lambda\ge w$ a real number. Then
--   $$(w-1)!\,\lambda^{-w}\sum_{k=0}^{w-1}\frac{\lambda^k}{k!}\le 2\lambda^{-1/2}.$$
--
--   Together with the first line of (2.5) this bounds $|S_\lambda h(w)|$ in the regime $\lambda\ge w$ (Lemma 3.3).
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 536, Lemma 3.1, (3.1)

import Mathlib
import Definitions.Def_PoissonDepTrials_MixSqrt_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixSqrt

/-- Chen (1975), Lemma 3.1, p. 536, (3.1): for `λ ≥ w` and `w ≥ 1`,
`(w − 1)! λ^{−w} Σ_{k=0}^{w−1} λ^k / k! ≤ 2λ^{−1/2}`. -/
theorem lemma_3_1 (lam : ℝ) (w : ℕ) (hw : 1 ≤ w) (hlw : (w : ℝ) ≤ lam) :
    ((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ * ∑ k ∈ Finset.range w, lam ^ k / (k.factorial : ℝ)
      ≤ 2 / Real.sqrt lam := by sorry

end PoissonDepTrials.MixSqrt
