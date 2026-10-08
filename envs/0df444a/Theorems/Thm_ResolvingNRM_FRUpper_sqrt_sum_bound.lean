-- Prove2me | Theorems.Thm_ResolvingNRM_FRUpper_sqrt_sum_bound
-- name    : ResolvingNRM.FRUpper.sqrt_sum_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:44:02.063673+00:00
-- url     : https://prove2.me/theorems/822b25e2-620a-4dde-b3d8-e9b4a0736268
-- title:
--   p. 36 — Σ_{t<T} √(Σ_{i<t} 1/(T−i−1)²) ≤ 2√T + √2
-- statement:
--   For every integer $T \ge 1$,
--   $$\sum_{t=0}^{T-1} \sqrt{\sum_{i=0}^{t-1} \frac{1}{(T - i - 1)^2}} \ \le\ 2\sqrt{T} + \sqrt{2}.$$
--
--   This is the analytic step of the proof of Proposition 3 that turns the per-period bounds of Lemma 8 into the $O(\sqrt{T})$ total: the $t$-th summand is of order $1/\sqrt{T - t}$, and these sum to order $\sqrt{T}$.
--
--   **Formalization Note.** For $t \le T - 1$ and $i \le t - 1$ the denominator $T - i - 1$ is at least $1$, so no division by zero occurs. An empty inner sum (at $t = 0$) is $0$.
-- source:
--   Bumpensanti, Wang, A Re-solving Heuristic with Uniformly Bounded Loss for Network Revenue Management, arXiv:1802.06192v3, App. C.2, chain of inequalities at the top of p. 36

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model
import Definitions.Def_ResolvingNRM_FRUpper_Model

open RLPBidPrice.Unbiased Matrix

namespace ResolvingNRM.FRUpper

/-- The summation chain of App. C.2, p. 36:
`∑_{t=0}^{T-1} √(∑_{i=0}^{t-1} 1 / (T − i − 1)²) ≤ 2√T + √2` for every integer `T ≥ 1`. -/
theorem sqrt_sum_bound (T : ℕ) (hT : 1 ≤ T) :
    ∑ t ∈ Finset.range T, Real.sqrt (∑ i ∈ Finset.range t, 1 / ((T : ℝ) - i - 1) ^ 2)
      ≤ 2 * Real.sqrt T + Real.sqrt 2 := by sorry

end ResolvingNRM.FRUpper
