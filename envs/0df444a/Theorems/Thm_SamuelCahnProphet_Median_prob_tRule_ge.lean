-- Prove2me | Theorems.Thm_SamuelCahnProphet_Median_prob_tRule_ge
-- name    : SamuelCahnProphet.Median.prob_tRule_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:21:50.314897+00:00
-- url     : https://prove2.me/theorems/76fdf0f3-b8b8-4a7e-bc07-dcebf0fd2a1d
-- title:
--   p. 1214, t(m) inequality — survival probability
-- statement:
--   Let $q=P(X_n^*<m)$ for measurable observations. For every index $i$,
--   $$
--   P(t(m)>i-1)\ge q.
--   $$
--   The bound supplies the termwise survival probability in the first inequality of the weak threshold display.
--
--   **Formalization Note** Indices are zero based in Lean, so the paper's event $s(m)>i-1$ or $t(m)>i-1$ becomes $i\le s(m)$ or $i\le t(m)$. Expectations are extended nonnegative integrals, and the final observation is always taken if no earlier one crosses the threshold.
-- source:
--   Samuel-Cahn, Comparison of threshold stop rules and maximum for independent nonnegative random variables, Ann. Probab. 12 (1984), p. 1214, first inequality of the t(m) display

import Mathlib
import Definitions.Def_SamuelCahnProphet_Median_Setting

namespace SamuelCahnProphet.Median

open MeasureTheory ProbabilityTheory

theorem prob_tRule_ge {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (m : ℝ) :
    ∀ i : Fin n, P {ω | maxX X ω < m} ≤ P {ω | i ≤ tRule X m ω} := by sorry
end SamuelCahnProphet.Median
