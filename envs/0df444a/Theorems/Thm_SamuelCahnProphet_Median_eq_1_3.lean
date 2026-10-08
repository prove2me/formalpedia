-- Prove2me | Theorems.Thm_SamuelCahnProphet_Median_eq_1_3
-- name    : SamuelCahnProphet.Median.eq_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:21:28.326115+00:00
-- url     : https://prove2.me/theorems/9c16449b-6d68-4211-97c2-c26e09a31544
-- title:
--   (1.3), p. 1214 — expected maximum bounded by threshold excess
-- statement:
--   For any real $m$ and a nonempty finite family of measurable observations $X_1,\ldots,X_n$ on a probability space, let $X_n^*=\max_i X_i$ and $\beta(m)=\sum_i E(X_i-m)^+$. Then
--   $$
--   E X_n^*\le m^+ + E(X_n^*-m)^+\le m^+ + \beta(m).
--   $$
--   Here the expectations are extended nonnegative expectations of positive parts; when $m\ge0$, the display is exactly the paper's (1.3). The bound supplies the upper estimate on the prophet's expected reward.
--
--   **Formalization Note** The statement allows arbitrary real $m$; $m^+$ is the extended nonnegative representation of the paper's $m$, which is nonnegative when $m$ is a median of nonnegative observations. Neither independence nor observation nonnegativity is needed for this inequality.
-- source:
--   Samuel-Cahn, Comparison of threshold stop rules and maximum for independent nonnegative random variables, Ann. Probab. 12 (1984), p. 1214, (1.3)

import Mathlib
import Definitions.Def_SamuelCahnProphet_Median_Setting

namespace SamuelCahnProphet.Median

open MeasureTheory ProbabilityTheory

theorem eq_1_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (m : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (maxX X ω) ∂P) ≤
        ENNReal.ofReal m + ∫⁻ ω, ENNReal.ofReal (maxX X ω - m) ∂P ∧
    ENNReal.ofReal m + (∫⁻ ω, ENNReal.ofReal (maxX X ω - m) ∂P) ≤
        ENNReal.ofReal m + beta P X m := by sorry
end SamuelCahnProphet.Median
