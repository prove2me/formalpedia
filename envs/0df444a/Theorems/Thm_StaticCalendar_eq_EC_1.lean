-- Prove2me | Theorems.Thm_StaticCalendar_eq_EC_1
-- name    : StaticCalendar.eq_EC_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:25:57.32941+00:00
-- url     : https://prove2.me/theorems/8afed90c-aa0c-4ad7-acc5-1edad6fa9c51
-- title:
--   (EC.1) — one-period Bernoulli comparison
-- statement:
--   Let $X_1$ be a random variable with values in $[0,1]$ and mean $p$, and let $Y_1$ be Bernoulli with mean $p$. For all $c\ge0$,
--
--   $$
--   \mathbb E[\min\{c,X_1\}]\ \ge\ \mathbb E[\min\{c,Y_1\}].
--   $$
--
--   Among laws on $[0,1]$ with a given mean, the Bernoulli law loses the most to truncation at any level.
--
--   Differences from the source:
--   - encoding: i.i.d. random variables on $[0,1]$ → their common law $\mu$ and, for the sum, the product measure; reason: the statement depends on the law only
--   - encoding: $\mathbb E[\min\{c,\mathrm{Bin}(T,p)\}]$ → the explicit binomial sum `binomMinExp`; reason: the definition of the expectation of a function of a binomial variable; same value
-- source:
--   Ma, Simchi-Levi & Zhao, Dynamic Pricing (and Assortment) under a Static Calendar, arXiv:1811.01077v5, (EC.1), p.ec5

import Mathlib
import Definitions.Def_StaticCalendar_binomMinExp

open MeasureTheory

namespace StaticCalendar

/-- (EC.1), arXiv:1811.01077v5, p.ec5: for `X₁ ∈ [0,1]` with mean `p`, `Y₁ ∼ Bernoulli(p)` and
`c ≥ 0`, `E[min{c,X₁}] ≥ E[min{c,Y₁}]`.

**Formalization Note.** Stated for the law `μ` of `X₁`; `binomMinExp 1 p c` is `E[min{c,Y₁}]`. -/
theorem eq_EC_1 (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : ∀ᵐ y ∂μ, y ∈ Set.Icc (0 : ℝ) 1)
    (c : ℝ) (hc : 0 ≤ c) :
    binomMinExp 1 (∫ y, y ∂μ) c ≤ ∫ y, min c y ∂μ := by sorry

end StaticCalendar
