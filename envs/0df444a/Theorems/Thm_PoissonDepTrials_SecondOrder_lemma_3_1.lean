-- Prove2me | Theorems.Thm_PoissonDepTrials_SecondOrder_lemma_3_1
-- name    : PoissonDepTrials.SecondOrder.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:38:58.48033+00:00
-- url     : https://prove2.me/theorems/ea42d4bf-96b7-4e85-886a-3b5f42961ce0
-- title:
--   Lemma 3.1, p. 536 — (w − 1)! λ^{−w} Σ_{k=0}^{w−1} λ^k/k! ≤ 2λ^{−½} for λ ≥ w ≥ 1
-- statement:
--   For a real $\lambda$ and an integer $w$ with $\lambda\ge w\ge1$,
--   $$(w-1)!\,\lambda^{-w}\sum_{k=0}^{w-1}\frac{\lambda^k}{k!}\le 2\lambda^{-1/2}.$$
--
--   This bounds the first representation of $S_\lambda h$ in (2.5) in the range $w\le\lambda$ and is one half of the proof of Lemma 3.3.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 536, Lemma 3.1, (3.1)

import Mathlib
import Definitions.Def_PoissonDepTrials_SecondOrder_Setting

open MeasureTheory ProbabilityTheory Finset

namespace PoissonDepTrials.SecondOrder

/-- Lemma 3.1, (3.1), p. 536: for `λ ≥ w` and `w ≥ 1`,
`(w − 1)! λ^{−w} Σ_{k=0}^{w−1} λ^k/k! ≤ 2λ^{−1/2}`. -/
theorem lemma_3_1 (lam : ℝ) (w : ℕ) (hw : 1 ≤ w) (hlw : (w : ℝ) ≤ lam) :
    ((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ * ∑ k ∈ Finset.range w, lam ^ k / (k.factorial : ℝ)
      ≤ 2 / Real.sqrt lam := by sorry

end PoissonDepTrials.SecondOrder
