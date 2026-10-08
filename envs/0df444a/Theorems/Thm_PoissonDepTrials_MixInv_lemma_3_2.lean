-- Prove2me | Theorems.Thm_PoissonDepTrials_MixInv_lemma_3_2
-- name    : PoissonDepTrials.MixInv.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:53:37.158394+00:00
-- url     : https://prove2.me/theorems/10845a51-67a1-4c3d-8874-d77d8270e0a6
-- title:
--   Lemma 3.2, p. 537 — (w − 1)! λ^{−w} Σ_{k≥w} λ^k/k! ≤ 2w^{−1/2} for 0 < λ ≤ w
-- statement:
--   For $0<\lambda\le w$ and an integer $w\ge1$,
--   $$(w-1)!\,\lambda^{-w}\sum_{k=w}^{\infty}\frac{\lambda^k}{k!}\le 2w^{-1/2}.$$
--   It controls the tail form of $S_\lambda h$ in the regime $\lambda\le w$.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), p. 537, Lemma 3.2, (3.2)

import Mathlib
import Definitions.Def_PoissonDepTrials_MixInv_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixInv

theorem lemma_3_2 (lam : ℝ) (hlam : 0 < lam) (w : ℕ) (hw : 1 ≤ w) (hlw : lam ≤ w) :
    ((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ * ∑' k : ℕ, lam ^ (k + w) / ((k + w).factorial : ℝ)
      ≤ 2 / Real.sqrt w := by sorry

end PoissonDepTrials.MixInv
