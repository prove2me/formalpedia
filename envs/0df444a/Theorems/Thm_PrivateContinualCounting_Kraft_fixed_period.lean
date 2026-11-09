-- Prove2me | Theorems.Thm_PrivateContinualCounting_Kraft_fixed_period
-- name    : PrivateContinualCounting.Kraft.fixed_period
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:01:28.273494+00:00
-- url     : https://prove2.me/theorems/d21e0c75-764b-4e9e-89a9-6fc02eb32f97
-- title:
--   Lemma A.1 — fixed-period divergence
-- statement:
--   Fix a positive period $p$ and an arbitrary countable internal coordinate set $I_0$. Let $M$ be a $p$-periodic Gaussian factorisation counter: its blocked matrices are lower-triangular block Toeplitz, their product is the prefix-sum matrix, all decoder rows and strategy columns lie in $\ell^2$, and its global factor sensitivity $\Delta$ is finite. Write $v_t=\Delta^2\|L_{t,\cdot}\|_2^2$ for normalized variance. Then
--   $$\lim_{t\to\infty}\frac{v_t}{(\ln t)^2}=+\infty.$$
--   The limit is over all positive integer times, including every output phase. It supplies the fixed-period clause of the full Kraft-law obstruction.
--
--   Differences from the source:
--   - encoding: positive input and release indices, coefficient indices starting at zero → stream coordinate j represents source j+1; a release indexed by t still means source time t; reason: This is a bijective reindexing; the optional time-zero release is the empty prefix with zero noise.
--   - encoding: fixed-period Gaussian counters with arbitrary countable inner coordinates → PeriodicCounter p I₀ contains the full square-summable factorisation and measurable L² decoder sums on the canonical independent Gaussian seed; reason: Every source counter is represented in law; the block Toeplitz identities include every phase and no within-block cutoff. The period is fixed before time varies.
--   - encoding: vₜ/(ln t)² tends to infinity → Tendsto of the quotient from natural-number atTop to real atTop; reason: This means eventually exceeding every real threshold along all times; the total log and division at t=0,1 affect no limit.
-- source:
--   Kisung Park, STOC 2027 submission #86 (October 2026), p. 18, PDF p. 20, Lemma A.1 (fixed period)

import Definitions.Def_PrivateContinualCounting_Kraft_PeriodicCounter

set_option autoImplicit false

namespace PrivateContinualCounting.Kraft

/-- Lemma A.1, printed 18 / PDF 20: the limit is along all times and every phase. -/
theorem fixed_period (p : ℕ) (I₀ : Type) [Countable I₀] (M : PeriodicCounter p I₀) :
    LogSqDiverges M.counter.variance := by sorry

end PrivateContinualCounting.Kraft
