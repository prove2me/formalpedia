-- Prove2me | Theorems.Thm_SamuelCahnProphet_Median_eq_t_display
-- name    : SamuelCahnProphet.Median.eq_t_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:21:59.234985+00:00
-- url     : https://prove2.me/theorems/6de2bbad-0518-4227-9765-dc2cd5a835a6
-- title:
--   p. 1214, t(m) display — weak-threshold reward identity
-- statement:
--   For measurable, mutually independent observations and $m\ge0$, put $q=P(X_n^*<m)$. The weak threshold rule satisfies
--   $$
--   E^+X_{t(m)}
--   =m(1-q)+\sum_{i=1}^n E(X_i-m)^+\,P(t(m)>i-1).
--   $$
--   This is the companion identity for the second branch of Theorem 1.
--
--   **Formalization Note** The paper states this identity in the $\beta\le m$ case. The identity itself holds without that case condition. The median supplies $m\ge0$ in the paper's setting. **Formalization Note** Indices are zero based in Lean, so the paper's event $s(m)>i-1$ or $t(m)>i-1$ becomes $i\le s(m)$ or $i\le t(m)$. Expectations are extended nonnegative integrals, and the final observation is always taken if no earlier one crosses the threshold.
-- source:
--   Samuel-Cahn, Comparison of threshold stop rules and maximum for independent nonnegative random variables, Ann. Probab. 12 (1984), p. 1214, display after (1.4)

import Mathlib
import Definitions.Def_SamuelCahnProphet_Median_Setting

namespace SamuelCahnProphet.Median

open MeasureTheory ProbabilityTheory

theorem eq_t_display {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) (m : ℝ) (hm : 0 ≤ m) :
    EplusT P X m = ENNReal.ofReal m * (1 - P {ω | maxX X ω < m}) +
      ∑ i : Fin n, (∫⁻ ω, ENNReal.ofReal (X i ω - m) ∂P) *
        P {ω | i ≤ tRule X m ω} := by sorry
end SamuelCahnProphet.Median
