-- Prove2me | Theorems.Thm_StaticCalendar_lemma_EC_3
-- name    : StaticCalendar.lemma_EC_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:26:06.019305+00:00
-- url     : https://prove2.me/theorems/67e027aa-96f5-4609-b575-5b8e97254bea
-- title:
--   Lemma EC.3 — Bernoulli replacement for truncated sums
-- statement:
--   Let $c>0$, let $T\ge1$, and let $X_1,\dots,X_T$ be i.i.d. random variables on $[0,1]$ with mean $p$. Let $Y_1,\dots,Y_T$ be i.i.d. Bernoulli variables with mean $p$. Then
--
--   $$
--   \mathbb E\Big[\min\Big\{c,\sum_{t=1}^TX_t\Big\}\Big]\ \ge\ \mathbb E\Big[\min\Big\{c,\sum_{t=1}^TY_t\Big\}\Big].
--   $$
--
--   This lets Step 2 replace each item's fractional demand by a binomial, whatever the demand law.
--
--   Differences from the source:
--   - encoding: i.i.d. random variables on $[0,1]$ → their common law $\mu$ and, for the sum, the product measure; reason: the statement depends on the law only
--   - encoding: $\mathbb E[\min\{c,\mathrm{Bin}(T,p)\}]$ → the explicit binomial sum `binomMinExp`; reason: the definition of the expectation of a function of a binomial variable; same value
--   - reading: "$p\in[0,1]$ be any positive fractional number" → $p$ is the mean of $\mu$, any value in $[0,1]$; reason: the printed phrase is ambiguous at $p=0$; the wider reading specializes to both
-- source:
--   Ma, Simchi-Levi & Zhao, Dynamic Pricing (and Assortment) under a Static Calendar, arXiv:1811.01077v5, Lemma EC.3, p.ec4

import Mathlib
import Definitions.Def_StaticCalendar_binomMinExp

open MeasureTheory

namespace StaticCalendar

/-- Lemma EC.3, arXiv:1811.01077v5, p.ec4: if `X₁,…,X_T` are i.i.d. on `[0,1]` with mean `p` and
`Y₁,…,Y_T` are i.i.d. Bernoulli(`p`), then for `c > 0`,
`E[min{c, Σₜ Xₜ}] ≥ E[min{c, Σₜ Yₜ}]`.

**Formalization Note.** Stated for the common law `μ` of the `Xₜ`; the sum of the `Yₜ` is `Bin(T,p)`,
so the right side is `binomMinExp T p c`. The mean `p = ∫ y ∂μ` ranges over all of `[0,1]`. -/
theorem lemma_EC_3 (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ y ∂μ, y ∈ Set.Icc (0 : ℝ) 1) (c : ℝ) (hc : 0 < c) (T : ℕ) (hT : 0 < T) :
    binomMinExp T (∫ y, y ∂μ) c ≤
      ∫ ω, min c (∑ t, ω t) ∂(Measure.pi fun _ : Fin T => μ) := by sorry

end StaticCalendar
