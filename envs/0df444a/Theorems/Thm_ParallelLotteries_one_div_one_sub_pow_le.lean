-- Prove2me | Theorems.Thm_ParallelLotteries_one_div_one_sub_pow_le
-- name    : ParallelLotteries.one_div_one_sub_pow_le
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:36:06.856607+00:00
-- url     : https://prove2.me/theorems/f3524390-5473-49cf-a3cc-d8d47d5006b0
-- title:
--   $\frac{1}{1-(1-1/k)^k}\le2-\frac1k$, strictly for $k\ge2$
-- statement:
--   For every integer $k\ge1$,
--   $$\frac{1}{1-(1-1/k)^k}\le 2-\frac1k,$$
--   and the inequality is strict for $k\ge2$.
--
--   The two sides coincide at $k=1$; for $k\ge2$ the single-item bound of (52) is strictly below the constant $2-1/k$ of Theorem 2.
--
--   Differences from the source:
--   - generalization: the display $\frac{1}{1-(1-1/k)^k}\le2-\frac1k$ (strict only "when $k=2$") → also strict for every $k\ge2$; reason: for $k\ge3$ the page's comparison $1-(1-1/k)^k\ge1-1/e\ge1/(2-1/k)$ holds strictly; the strict form is what the strict conclusion of Theorem 2 needs, and it implies the printed inequality
-- source:
--   Arnosti–Randolph, Alaskan Hunting License Lotteries Are Flexible and Approximately Efficient, SSRN 3370605 (preprint), App. D.2, display at the top of p.33 and the sentence after it

import Mathlib

namespace ParallelLotteries

/-- **Comparison of the single-item bound with `2 − 1/k`** — Arnosti–Randolph, SSRN 3370605
(preprint), App. D.2, display at the top of p.33: "we have that 1/(1 − (1 − 1/k)^k) ≤ 2 − 1/k, as
the expressions coincide for k = 1, the lefthand side is strictly lesser when k = 2, and finally
1 − (1 − 1/k)^k ≥ 1 − 1/e ≥ 1/(2 − 1/k) when k ≥ 3."

For every integer `k ≥ 1`, `1/(1 − (1 − 1/k)^k) ≤ 2 − 1/k`, and the inequality is strict when
`k ≥ 2`.

**Formalization Note.** `1/k` is real division. The strict clause for `k ≥ 2` is what the page's
case analysis shows ("strictly lesser when k = 2", and for `k ≥ 3` the bound `1 − 1/e` gives a
strict inequality) and what the proof of Theorem 2 needs for its strict conclusion. -/
theorem one_div_one_sub_pow_le (k : ℕ) (hk : 1 ≤ k) :
    1 / (1 - (1 - 1 / (k : ℝ)) ^ k) ≤ 2 - 1 / (k : ℝ) ∧
    (2 ≤ k → 1 / (1 - (1 - 1 / (k : ℝ)) ^ k) < 2 - 1 / (k : ℝ)) := by sorry

end ParallelLotteries
