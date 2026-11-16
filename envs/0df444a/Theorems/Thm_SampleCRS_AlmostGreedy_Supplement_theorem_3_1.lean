-- Prove2me | Theorems.Thm_SampleCRS_AlmostGreedy_Supplement_theorem_3_1
-- name    : SampleCRS.AlmostGreedy.Supplement.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:36:43.918821+00:00
-- url     : https://prove2.me/theorems/3af85d7d-a7e5-441c-afe5-38f591275cbe
-- title:
--   Theorem 3.1 — single-item Conservative Scaling
-- statement:
--   Let $n$ be any finite ground-set size, and let the unknown activation probabilities satisfy $0\le p_i\le1$ and $\sum_i p_i=1$. Algorithm 1 scans an independent uniform random order and accepts the first active element passing its sample-dependent coin: it always passes a sample-inactive element and passes a sample-active one with probability $1-1/e$.
--
--   For every realization the output is an active subset of cardinality at most one, and for every $i$ with $p_i>0$,
--   $$C_i=\Pr[i\text{ accepted}\mid X_i=1]\ge1-1/e.$$
--   The probability averages the online activations, samples, independent coins and uniform order. This is the specified single-item run, separate from Algorithm 4.
--
--   Differences from the source:
--   - encoding: elements 1,…,n and independent Bernoulli trials → Fin n and finite product-weight expectations; reason: the label shift is a bijection and the weights are exactly the independent Bernoulli law
-- source:
--   Shaddin Dughmi, Vasilis Livanos, Pranav Nuti, STOC 2027 submission #686 (October 2026), Theorem 3.1, p. 6

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_Supplement_scaling

namespace SampleCRS.AlmostGreedy.Supplement

/-- Theorem 3.1, p.6. single-item Conservative Scaling. -/
theorem theorem_3_1 {n : ℕ} (p : Fin n → ℝ) (hp : ValidProb p) (hmass : (∑ i, p i) = 1) :
    ScalingFeasible n 1 ∧
    ∀ i, 0 < p i → 1 - 1 / Real.exp 1 ≤ scalingC 1 (1 - 1 / Real.exp 1) p i := by sorry

end SampleCRS.AlmostGreedy.Supplement
