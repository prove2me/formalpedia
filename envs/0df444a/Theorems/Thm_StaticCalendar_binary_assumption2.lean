-- Prove2me | Theorems.Thm_StaticCalendar_binary_assumption2
-- name    : StaticCalendar.binary_assumption2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:26:48.528502+00:00
-- url     : https://prove2.me/theorems/d9fd4457-6c2a-4d64-af1a-5f064fcb2340
-- title:
--   p.13 and p.ec11 — $\{0,1\}$-demand satisfies Assumption 2
-- statement:
--   Suppose every demand quantity is almost surely $0$ or $1$. Then Assumption 2 holds:
--
--   $$
--   \frac{\mathbb E[\min\{c,Q\}]}{\mathbb E[Q]}\ge\frac{\mathbb E[\min\{c,Q'\}]}{\mathbb E[Q']}\qquad\text{for all } c\in[0,1].
--   $$
--
--   This is why Theorem 1 needs Assumption 2 only for fractional demand.
--
--   Differences from the source:
--   - encoding: Assumption 2 as a ratio of expectations → the cross-multiplied form `Assumption2`; reason: equivalent when both means are positive; the ratio is undefined otherwise and the product form reads $0\le0$
-- source:
--   Ma, Simchi-Levi & Zhao, Dynamic Pricing (and Assortment) under a Static Calendar, arXiv:1811.01077v5, p.13 ("it automatically holds for {0,1}-demand"); p.ec11 ("which naturally satisfies Assumption 2")

import Mathlib
import Definitions.Def_StaticCalendar_Assumption2
import Definitions.Def_StaticCalendar_BinaryDemand

open MeasureTheory

namespace StaticCalendar

/-- `{0,1}`-demand satisfies Assumption 2, arXiv:1811.01077v5, p.13 ("it automatically holds for
{0,1}-demand") and p.ec11 ("condition (i) is integral, Bernoulli demand, which naturally satisfies
Assumption 2"). -/
theorem binary_assumption2 {n m : ℕ} (I : DemandModel n m) (h : BinaryDemand I) :
    Assumption2 I := by sorry

end StaticCalendar
