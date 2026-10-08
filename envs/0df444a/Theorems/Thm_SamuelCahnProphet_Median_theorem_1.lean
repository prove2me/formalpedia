-- Prove2me | Theorems.Thm_SamuelCahnProphet_Median_theorem_1
-- name    : SamuelCahnProphet.Median.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:21:57.47598+00:00
-- url     : https://prove2.me/theorems/4c8753b4-16ea-4504-8dab-fb8172344f50
-- title:
--   Theorem 1, p. 1214 — a median threshold earns half the expected maximum
-- statement:
--   Let $X_1,\ldots,X_n$ be independent nonnegative random variables, $n\ge1$, let $X_n^*=\max_iX_i$, and let $m$ be a median of $X_n^*$. Write $\beta=\sum_iE(X_i-m)^+$. Then both conditional conclusions hold:
--   $$
--   \begin{aligned}
--   \beta\ge m&\implies E X_n^*\le 2E^+X_{s(m)}\le2E X_{s(m)},\\
--   \beta\le m&\implies E X_n^*\le 2E^+X_{t(m)}\le2E X_{t(m)}.
--   \end{aligned}
--   $$
--   Thus one of the two median threshold rules guarantees at least half the expected maximum, with the positive stopped reward explicitly retained.
--
--   **Formalization Note** Nonnegativity is almost sure, independence is mutual, and expectations take values in $[0,\infty]$, so no integrability condition is imposed. **Formalization Note** Indices are zero based in Lean, so the paper's event $s(m)>i-1$ or $t(m)>i-1$ becomes $i\le s(m)$ or $i\le t(m)$. Expectations are extended nonnegative integrals, and the final observation is always taken if no earlier one crosses the threshold.
-- source:
--   Samuel-Cahn, Comparison of threshold stop rules and maximum for independent nonnegative random variables, Ann. Probab. 12 (1984), p. 1214, Theorem 1

import Mathlib
import Definitions.Def_SamuelCahnProphet_Median_Setting

namespace SamuelCahnProphet.Median

open MeasureTheory ProbabilityTheory

theorem theorem_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hXnn : ∀ i, ∀ᵐ ω ∂P, 0 ≤ X i ω) (hind : iIndepFun X P) (m : ℝ)
    (hmed : IsMedian P (maxX X) m) :
    (ENNReal.ofReal m ≤ beta P X m →
      (∫⁻ ω, ENNReal.ofReal (maxX X ω) ∂P) ≤ 2 * EplusS P X m ∧
      2 * EplusS P X m ≤ 2 * expStop P X (sRule X m)) ∧
    (beta P X m ≤ ENNReal.ofReal m →
      (∫⁻ ω, ENNReal.ofReal (maxX X ω) ∂P) ≤ 2 * EplusT P X m ∧
      2 * EplusT P X m ≤ 2 * expStop P X (tRule X m)) := by sorry
end SamuelCahnProphet.Median
