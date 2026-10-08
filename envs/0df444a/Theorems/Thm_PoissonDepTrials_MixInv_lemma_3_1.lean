-- Prove2me | Theorems.Thm_PoissonDepTrials_MixInv_lemma_3_1
-- name    : PoissonDepTrials.MixInv.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:40:02.34183+00:00
-- url     : https://prove2.me/theorems/6e2ef7cf-b2de-494a-826c-6a2763b8e702
-- title:
--   Lemma 3.1, p. 536 — (w − 1)! λ^{−w} Σ_{k=0}^{w−1} λ^k/k! ≤ 2λ^{−1/2} for λ ≥ w ≥ 1
-- statement:
--   For real $\lambda$ and an integer $w$ with $\lambda\ge w\ge1$,
--   $$(w-1)!\,\lambda^{-w}\sum_{k=0}^{w-1}\frac{\lambda^k}{k!}\le 2\lambda^{-1/2}.$$
--   Together with Lemma 3.2 it gives the bound $\|S_\lambda h\|\le4\|h\|\min(\lambda^{-1/2},1)$ of Lemma 3.3.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 536, Lemma 3.1, (3.1)

import Mathlib
import Definitions.Def_PoissonDepTrials_MixInv_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixInv

theorem lemma_3_1 (lam : ℝ) (w : ℕ) (hw : 1 ≤ w) (hlw : (w : ℝ) ≤ lam) :
    ((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ * ∑ k ∈ Finset.range w, lam ^ k / (k.factorial : ℝ)
      ≤ 2 / Real.sqrt lam := by sorry

end PoissonDepTrials.MixInv
