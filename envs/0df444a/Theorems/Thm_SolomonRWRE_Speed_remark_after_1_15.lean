-- Prove2me | Theorems.Thm_SolomonRWRE_Speed_remark_after_1_15
-- name    : SolomonRWRE.Speed.remark_after_1_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:44:07.749995+00:00
-- url     : https://prove2.me/theorems/31c83d68-bb2f-45ca-934f-454f6ebe8d3c
-- title:
--   §1 remark after (1.15) — Eσ < 1 forces transience to +∞
-- statement:
--   For the annealed nearest-neighbor walk in an independent, identically distributed environment, suppose $E\sigma<1$, where $\sigma=(1-\alpha_0)/\alpha_0$. Then
--
--   $$
--   X_n\longrightarrow +\infty\qquad\text{almost surely}.
--   $$
--
--   This observation identifies the direction of escape in the positive-speed regime and supplies the passage-time setting used later in Section 1.
--
--   **Formalization Note** The expectation is an extended nonnegative integral, so the hypothesis implies its finiteness.
-- source:
--   Solomon, Random Walks in a Random Environment, Ann. Probab. 3(1):1–31 (1975), DOI 10.1214/aop/1176996444, p. 6, §1, remark after Theorem (1.15)

import Mathlib
import Definitions.Def_SolomonRWRE_Speed_Model

namespace SolomonRWRE.Speed

/-- Solomon (1975), p. 6, remark after Theorem (1.15). -/
theorem remark_after_1_15 {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (α : ℤ → Ω → ℝ) (X : ℕ → Ω → ℤ) (h : SolomonRWRE.Recurrence.IsRWRE P α X)
    (hσ : meanSigma P α < 1) :
    ∀ᵐ ω ∂P, Filter.Tendsto (fun n => X n ω) Filter.atTop Filter.atTop := by sorry

end SolomonRWRE.Speed
