-- Prove2me | Theorems.Thm_StaticCalendar_lemma_EC_6
-- name    : StaticCalendar.lemma_EC_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:26:36.099218+00:00
-- url     : https://prove2.me/theorems/ffe9064f-f420-4cfd-a26b-23108b6a0942
-- title:
--   Lemma EC.6 — $\Delta^{APX}$ is monotone in $b$
-- statement:
--   Let $T\ge1$ be an integer. For real numbers with $T\ge x\ge y>0$,
--
--   $$
--   \frac{\mathbb E[\min\{\mathrm{Bin}(T,x/T),x\}]}{x}\ \ge\ \frac{\mathbb E[\min\{\mathrm{Bin}(T,y/T),y\}]}{y}.
--   $$
--
--   The guarantee only improves with more inventory, for real inventories. It moves Step 2 from $b_i$ down to $\min_ib_i$, and it reduces (10) to the integer case.
--
--   Differences from the source:
--   - encoding: $\mathbb E[\min\{c,\mathrm{Bin}(T,p)\}]$ → the explicit binomial sum `binomMinExp`; reason: the definition of the expectation of a function of a binomial variable; same value
-- source:
--   Ma, Simchi-Levi & Zhao, Dynamic Pricing (and Assortment) under a Static Calendar, arXiv:1811.01077v5, Lemma EC.6, p.ec5

import Mathlib
import Definitions.Def_StaticCalendar_deltaAPX

open MeasureTheory

namespace StaticCalendar

/-- Lemma EC.6, arXiv:1811.01077v5, p.ec5: for real `T ≥ x ≥ y > 0`,
`E[min{Bin(T,x/T),x}]/x ≥ E[min{Bin(T,y/T),y}]/y`. -/
theorem lemma_EC_6 (T : ℕ) (hT : 0 < T) (x y : ℝ) (hxT : x ≤ T) (hyx : y ≤ x) (hy : 0 < y) :
    deltaAPX T y ≤ deltaAPX T x := by sorry

end StaticCalendar
