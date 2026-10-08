-- Prove2me | Theorems.Thm_SamuelCahnProphet_Median_eq_1_4_first
-- name    : SamuelCahnProphet.Median.eq_1_4_first
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:22:56.531986+00:00
-- url     : https://prove2.me/theorems/3a367f85-3517-4fb1-89d3-f12fc1ed02b7
-- title:
--   (1.4), first equality — strict-threshold reward split
-- statement:
--   Let $m\ge0$. For measurable observations $X_1,\ldots,X_n$, let $s(m)$ be the first index before $n$ with $X_i>m$, or $n$ otherwise, and let $p=P(X_n^*>m)$. Then
--   $$
--   E^+X_{s(m)}=mp+E(X_{s(m)}-m)^+.
--   $$
--   This separates the threshold level from the excess reward in (1.4).
--
--   **Formalization Note** The paper obtains $m\ge0$ from its nonnegative observations and median condition; the identity states just that necessary sign condition. **Formalization Note** Indices are zero based in Lean, so the paper's event $s(m)>i-1$ or $t(m)>i-1$ becomes $i\le s(m)$ or $i\le t(m)$. Expectations are extended nonnegative integrals, and the final observation is always taken if no earlier one crosses the threshold.
-- source:
--   Samuel-Cahn, Comparison of threshold stop rules and maximum for independent nonnegative random variables, Ann. Probab. 12 (1984), p. 1214, (1.4), first equality

import Mathlib
import Definitions.Def_SamuelCahnProphet_Median_Setting

namespace SamuelCahnProphet.Median

open MeasureTheory ProbabilityTheory

theorem eq_1_4_first {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (m : ℝ) (hm : 0 ≤ m) :
    EplusS P X m = ENNReal.ofReal m * P {ω | m < maxX X ω} +
      ∫⁻ ω, ENNReal.ofReal (X (sRule X m ω) ω - m) ∂P := by sorry
end SamuelCahnProphet.Median
