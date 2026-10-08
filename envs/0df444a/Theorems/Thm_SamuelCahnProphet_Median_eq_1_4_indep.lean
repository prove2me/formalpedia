-- Prove2me | Theorems.Thm_SamuelCahnProphet_Median_eq_1_4_indep
-- name    : SamuelCahnProphet.Median.eq_1_4_indep
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:21:44.729552+00:00
-- url     : https://prove2.me/theorems/37be0a7e-4172-4ffc-b018-b2d7412021cf
-- title:
--   (1.4), fourth equality — factorization by independence
-- statement:
--   Let $X_1,\ldots,X_n$ be measurable and mutually independent. For every $i$ and real $m$,
--   $$
--   E\!\left[(X_i-m)^+\,\mathbf1_{\{s(m)>i-1\}}\right]
--   =E(X_i-m)^+\,P(s(m)>i-1).
--   $$
--   This is the independence step in the fourth equality of (1.4).
--
--   **Formalization Note** Indices are zero based in Lean, so the paper's event $s(m)>i-1$ or $t(m)>i-1$ becomes $i\le s(m)$ or $i\le t(m)$. Expectations are extended nonnegative integrals, and the final observation is always taken if no earlier one crosses the threshold.
-- source:
--   Samuel-Cahn, Comparison of threshold stop rules and maximum for independent nonnegative random variables, Ann. Probab. 12 (1984), p. 1214, (1.4), fourth equality and following sentence

import Mathlib
import Definitions.Def_SamuelCahnProphet_Median_Setting

namespace SamuelCahnProphet.Median

open MeasureTheory ProbabilityTheory

theorem eq_1_4_indep {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) (m : ℝ) :
    ∀ i : Fin n,
      (∫⁻ ω, (if i ≤ sRule X m ω then ENNReal.ofReal (X i ω - m) else 0) ∂P) =
        (∫⁻ ω, ENNReal.ofReal (X i ω - m) ∂P) * P {ω | i ≤ sRule X m ω} := by sorry
end SamuelCahnProphet.Median
