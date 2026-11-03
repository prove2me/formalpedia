-- Prove2me | Theorems.Thm_StaticCalendar_lemma_EC_5
-- name    : StaticCalendar.lemma_EC_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:26:03.481845+00:00
-- url     : https://prove2.me/theorems/275daccd-2410-4f21-ba46-fb3e63121da9
-- title:
--   Lemma EC.5 — the truncated binomial per unit of mean
-- statement:
--   Let $c>0$ and let $T\ge1$ be an integer. The function
--
--   $$
--   f(x)=\frac{\mathbb E[\min\{c,\mathrm{Bin}(T,x)\}]}{Tx}
--   $$
--
--   is non-increasing on $(0,1]$. Raising the success probability lowers the fraction of the mean that survives truncation at $c$. It moves Step 2 from $\rho_i$ up to the LP bound $b_i/T$.
--
--   Differences from the source:
--   - encoding: $\mathbb E[\min\{c,\mathrm{Bin}(T,p)\}]$ → the explicit binomial sum `binomMinExp`; reason: the definition of the expectation of a function of a binomial variable; same value
-- source:
--   Ma, Simchi-Levi & Zhao, Dynamic Pricing (and Assortment) under a Static Calendar, arXiv:1811.01077v5, Lemma EC.5, p.ec5

import Mathlib
import Definitions.Def_StaticCalendar_binomMinExp

open MeasureTheory

namespace StaticCalendar

/-- Lemma EC.5, arXiv:1811.01077v5, p.ec5: for `c > 0` and `T ≥ 1`, the function
`f(x) = E[min{c, Bin(T,x)}] / (Tx)` is non-increasing on `(0,1]`. -/
theorem lemma_EC_5 (c : ℝ) (hc : 0 < c) (T : ℕ) (hT : 0 < T) :
    AntitoneOn (fun y : ℝ => binomMinExp T y c / (T * y)) (Set.Ioc 0 1) := by sorry

end StaticCalendar
