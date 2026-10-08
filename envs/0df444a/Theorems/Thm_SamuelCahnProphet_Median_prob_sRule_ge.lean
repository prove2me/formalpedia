-- Prove2me | Theorems.Thm_SamuelCahnProphet_Median_prob_sRule_ge
-- name    : SamuelCahnProphet.Median.prob_sRule_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:21:45.878208+00:00
-- url     : https://prove2.me/theorems/985f1cf3-3c39-40e8-8606-c8c975010bbc
-- title:
--   (1.4), first inequality — survival probability for s(m)
-- statement:
--   Let $p=P(X_n^*>m)$ for measurable observations. Every index $i$ satisfies
--   $$
--   P(s(m)>i-1)\ge 1-p.
--   $$
--   If no observation exceeds $m$, the strict threshold rule reaches every index, giving the termwise probability bound used in the first inequality of (1.4).
--
--   **Formalization Note** Indices are zero based in Lean, so the paper's event $s(m)>i-1$ or $t(m)>i-1$ becomes $i\le s(m)$ or $i\le t(m)$. Expectations are extended nonnegative integrals, and the final observation is always taken if no earlier one crosses the threshold.
-- source:
--   Samuel-Cahn, Comparison of threshold stop rules and maximum for independent nonnegative random variables, Ann. Probab. 12 (1984), p. 1214, (1.4), first inequality

import Mathlib
import Definitions.Def_SamuelCahnProphet_Median_Setting

namespace SamuelCahnProphet.Median

open MeasureTheory ProbabilityTheory

theorem prob_sRule_ge {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (m : ℝ) :
    ∀ i : Fin n, 1 - P {ω | m < maxX X ω} ≤ P {ω | i ≤ sRule X m ω} := by sorry
end SamuelCahnProphet.Median
