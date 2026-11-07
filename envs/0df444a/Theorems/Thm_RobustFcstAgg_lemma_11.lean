-- Prove2me | Theorems.Thm_RobustFcstAgg_lemma_11
-- name    : RobustFcstAgg.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:43:21.73119+00:00
-- url     : https://prove2.me/theorems/37412900-2c3a-4200-97f4-3f875b0e6f5f
-- title:
--   Lemma 11 — grid minimum $\ge(1-d^2/(n-1))\cdot$ interval minimum
-- statement:
--   For $n\ge2$ both minima exist and
--   $$\min_{p\in P_d,\ p(0)=1}\ \max_{t\in\{1,\dots,n\}}|p(t)|\ \ge\ \Bigl(1-\frac{d^2}{n-1}\Bigr)\min_{p\in P_d,\ p(0)=1}\ \max_{x\in[1,n]}|p(x)|.$$
--
--   This transfers the continuous value to the integer grid, and gives the lower bound on the discrete problem.
--
--   Differences from the source:
--   - encoding: n unrestricted in q(n) and d²/(n−1) → 2 ≤ n; reason: those expressions are undefined at n = 1
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Lemma 11, p.29; proof pp.29–30

import Mathlib
import Definitions.Def_RobustFcstAgg_gridAbsSet
import Definitions.Def_RobustFcstAgg_ivlSet

namespace RobustFcstAgg

/-- **Lemma 11.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Lemma 11, p.29 (proof pp.29–30):
`min_{p ∈ P_d, p(0) = 1} max_{t ∈ {1,…,n}} |p(t)| ≥ (1 − d²/(n − 1)) min_{p ∈ P_d, p(0) = 1} max_{x ∈ [1,n]} |p(x)|`.

**Formalization Note.** `n ≥ 2`, since `d²/(n − 1)` is undefined at `n = 1`. Both minima are attained. There is no hypothesis
`d² ≤ n − 1`: a negative left factor makes the inequality trivial. -/
theorem lemma_11 (n d : ℕ) (hn : 2 ≤ n) :
    ∃ a b : ℝ, IsLeast (gridAbsSet n d) a ∧ IsLeast (ivlSet n d) b ∧
      (1 - (d : ℝ) ^ 2 / ((n : ℝ) - 1)) * b ≤ a := by sorry

end RobustFcstAgg
