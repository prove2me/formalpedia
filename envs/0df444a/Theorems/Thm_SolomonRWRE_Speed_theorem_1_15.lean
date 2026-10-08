-- Prove2me | Theorems.Thm_SolomonRWRE_Speed_theorem_1_15
-- name    : SolomonRWRE.Speed.theorem_1_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:44:17.303918+00:00
-- url     : https://prove2.me/theorems/30c83d14-6050-4bb9-bbcd-5abd0206fe76
-- title:
--   Theorem (1.15) — mean ladder time
-- statement:
--   For the annealed walk, let $\tau_1$ be the first passage time from zero to one and let $e=E\sigma$, where $\sigma=(1-\alpha_0)/\alpha_0$. Then
--
--   $$
--   E\tau_1=\begin{cases}\dfrac{1+e}{1-e},&e<1,\\[4pt]
--   \infty,&e\ge1.\end{cases}
--   $$
--
--   The formula identifies the threshold for finite mean ladder time, which controls the positive-speed regime.
--
--   **Formalization Note** Both expectations are extended nonnegative. The real quotient is used only under $e<1$.
-- source:
--   Solomon, Random Walks in a Random Environment, Ann. Probab. 3(1):1–31 (1975), DOI 10.1214/aop/1176996444, p. 6, Theorem (1.15)

import Mathlib
import Definitions.Def_SolomonRWRE_Speed_Model

namespace SolomonRWRE.Speed

/-- Solomon (1975), p. 6, Theorem (1.15). The expected first positive
passage time is finite with the displayed value precisely when `Eσ < 1`,
and infinite when `Eσ ≥ 1`. -/
theorem theorem_1_15 {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (α : ℤ → Ω → ℝ) (X : ℕ → Ω → ℤ) (h : SolomonRWRE.Recurrence.IsRWRE P α X) :
    (meanSigma P α < 1 →
      (∫⁻ ω, ENat.toENNReal (ladderTime X 1 ω) ∂P) =
        ENNReal.ofReal ((1 + (meanSigma P α).toReal) /
          (1 - (meanSigma P α).toReal))) ∧
    (1 ≤ meanSigma P α →
      (∫⁻ ω, ENat.toENNReal (ladderTime X 1 ω) ∂P) = ⊤) := by sorry

end SolomonRWRE.Speed
