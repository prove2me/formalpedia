-- Prove2me | Theorems.Thm_PrivateContinualCounting_Kraft_kraft_law
-- name    : PrivateContinualCounting.Kraft.kraft_law
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:02:34.84687+00:00
-- url     : https://prove2.me/theorems/f404c8da-6670-40d5-b505-4961ca53acd7
-- title:
--   Theorem 1.1 — the full Kraft law for time-invariant counters
-- statement:
--   A counter is one infinite Gaussian factorisation mechanism with finite factor sensitivity, released from one stream-independent Gaussian seed. Its normalized variance is $v_t=\mu^2\operatorname{Var}(Y_t-S_t)$, equivalently the exact coefficient formula at unit Gaussian privacy. Theorem 1.1 asserts both of the following.
--
--   1. Every scalar or vector real time-invariant counter, and every Gaussian counter with any fixed positive period and arbitrary countable internal coordinates, satisfies
--   $$\lim_{t\to\infty}\frac{v_t}{(\ln t)^2}=+\infty.$$
--   2. For every real nondecreasing doubling envelope $g:[1,\infty)\to[1,\infty)$,
--   $$\left[\exists\text{ bounded-sensitivity scalar/vector LTI counter},\ \exists C>0\ \forall t\ge3:\ v_t\le C(\ln t)^2g(\ln t)\right]
--   \quad\Longleftrightarrow\quad \sum_{k=0}^\infty\frac1{g(2^k)}<\infty.$$
--   If the series converges, a scalar counter with real coefficients suffices. The same $C$ works at every indicated time, and may depend on $g$ and the counter. Both iff directions are stated; necessity does not assume the Kraft condition. Complex formal factors in the supporting theorem yield actual real vector mechanisms by the source's norm-preserving realification. This goal characterizes the entire class in the source rather than an arbitrary variance sequence or a finite-horizon family.
--
--   Differences from the source:
--   - encoding: positive input and release indices, coefficient indices starting at zero → stream coordinate j represents source j+1; a release indexed by t still means source time t; reason: This is a bijective reindexing; the optional time-zero release is the empty prefix with zero noise.
--   - encoding: scalar or vector real Gaussian factorisation counters → LTICounter m is an exact-convolution coefficient pair with summable strategy energy and its canonical infinite-product Gaussian release rule; reason: Every source coefficient pair has this real Gaussian realization; no decoder summability, sign, rationality or smoothness is imposed. Normalized variance uses the source coefficient formula.
--   - encoding: fixed-period Gaussian counters with arbitrary countable inner coordinates → PeriodicCounter p I₀ contains the full square-summable factorisation and measurable L² decoder sums on the canonical independent Gaussian seed; reason: Every source counter is represented in law; the block Toeplitz identities include every phase and no within-block cutoff. The period is fixed before time varies.
--   - encoding: g defined on the real half-line [1,∞) → g is a function on ℝ with every envelope condition restricted to [1,∞); reason: Values below 1 are unused in all claims; monotonicity and doubling allow discontinuities.
--   - encoding: vₜ/(ln t)² tends to infinity → Tendsto of the quotient from natural-number atTop to real atTop; reason: This means eventually exceeding every real threshold along all times; the total log and division at t=0,1 affect no limit.
--   - encoding: some finite constant C in the all-time bound → an existential positive real C chosen before every t≥3; reason: Any source bound can be enlarged to a positive C, without changing which envelopes are achievable.
-- source:
--   Kisung Park, STOC 2027 submission #86 (October 2026), p. 1, PDF p. 3, Theorem 1.1 (i)–(ii); Kisung Park, STOC 2027 submission #86 (October 2026), p. 8, PDF p. 10, §3.2, displayed Hilbert-block estimates, and §3.3; Kisung Park, STOC 2027 submission #86 (October 2026), p. 18, PDF p. 20, Appendix A

import Definitions.Def_PrivateContinualCounting_Kraft_LTIFactors
import Definitions.Def_PrivateContinualCounting_Kraft_PeriodicCounter
import Definitions.Def_PrivateContinualCounting_Kraft_Envelopes

set_option autoImplicit false

namespace PrivateContinualCounting.Kraft

/-- Theorem 1.1 in full. LTICounter supplies the actual one-seed infinite Gaussian
release rule of Definition 2.2; PeriodicCounter includes the countable L² realization.
Variance is the exact coefficient definition of unit-GDP normalized variance. -/
theorem kraft_law :
    ((∀ (m : ℕ) (M : LTICounter m), LogSqDiverges M.val.variance) ∧
      (∀ (p : ℕ) (I₀ : Type) [Countable I₀] (M : PeriodicCounter p I₀),
        LogSqDiverges M.counter.variance)) ∧
    (∀ (g : ℝ → ℝ), IsEnvelope g →
      ((∃ (m : ℕ) (M : LTICounter m), HasEnvelope M.val.variance g) ↔ KraftCondition g) ∧
      (KraftCondition g → ∃ M : LTICounter 1, HasEnvelope M.val.variance g)) := by sorry

end PrivateContinualCounting.Kraft
