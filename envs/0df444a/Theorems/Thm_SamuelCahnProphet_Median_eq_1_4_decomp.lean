-- Prove2me | Theorems.Thm_SamuelCahnProphet_Median_eq_1_4_decomp
-- name    : SamuelCahnProphet.Median.eq_1_4_decomp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:21:37.011837+00:00
-- url     : https://prove2.me/theorems/f6279265-dee3-4cf4-bb23-17b045205347
-- title:
--   (1.4), second and third equalities — excess decomposition
-- statement:
--   For measurable observations and any real $m$, the excess reward under the strict threshold rule decomposes as
--   $$
--   E(X_{s(m)}-m)^+
--   =\sum_{i=1}^n E\!\left[(X_i-m)^+\,\mathbf1_{\{s(m)>i-1\}}\right].
--   $$
--   This is the pathwise part of (1.4), before independence factors the terms.
--
--   **Formalization Note** The paper passes through the indicator of $\{s(m)=i\}$; this statement records the resulting equality without the common $mp$ summand. **Formalization Note** Indices are zero based in Lean, so the paper's event $s(m)>i-1$ or $t(m)>i-1$ becomes $i\le s(m)$ or $i\le t(m)$. Expectations are extended nonnegative integrals, and the final observation is always taken if no earlier one crosses the threshold.
-- source:
--   Samuel-Cahn, Comparison of threshold stop rules and maximum for independent nonnegative random variables, Ann. Probab. 12 (1984), p. 1214, (1.4), second and third equalities

import Mathlib
import Definitions.Def_SamuelCahnProphet_Median_Setting

namespace SamuelCahnProphet.Median

open MeasureTheory ProbabilityTheory

theorem eq_1_4_decomp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (m : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (X (sRule X m ω) ω - m) ∂P) =
      ∑ i : Fin n, ∫⁻ ω, (if i ≤ sRule X m ω
        then ENNReal.ofReal (X i ω - m) else 0) ∂P := by sorry
end SamuelCahnProphet.Median
