-- Prove2me | Theorems.Thm_StoneRegression_Quantile_corollary_1_necessity
-- name    : StoneRegression.Quantile.corollary_1_necessity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:20:57.199546+00:00
-- url     : https://prove2.me/theorems/a07a1109-1e86-4930-91e2-a8fc59f63047
-- title:
--   Corollary 1 (necessity), p. 598 — consistent probability weights satisfy (1), (3) and (5)
-- statement:
--   Let $\{W_n\}$ be a sequence of probability weights (with jointly Borel weight functions) on $\mathbb R^d$, and let $X, X_1, X_2,\dots$ be i.i.d. with law $\mu$. If $\{W_n\}$ is consistent, then the following three conditions hold:
--   1. there is a $C\ge1$ such that for every nonnegative Borel function $f$ on $\mathbb R^d$
--   $$E\sum_i W_{ni}(X)f(X_i)\le C\,Ef(X)\qquad\text{for all } n\ge1;$$
--   2. $\sum_i W_{ni}(X)\,I_{\{\|X_i-X\|>a\}}\to0$ in probability for every $a>0$;
--   3. $\max_i W_{ni}(X)\to0$ in probability.
--
--   This is the necessity half of Corollary 1: for probability weights, consistency forces the three conditions. The mission uses it to make conditions (1) and (3) available, through Propositions 4 and 15, when proving Theorem 3 from consistency alone.
--
--   **Formalization Note.** The sufficiency half of Corollary 1 is a milestone of the companion mission on nearest-neighbor weights; both halves are special cases of Theorem 1, the goal of the first mission of this series, and are posed again here because drafts cannot import drafts. The conditions are stated with $|W_{ni}|$ (the form of Theorem 1), which equals $W_{ni}$ for probability weights. The weight functions are assumed jointly Borel.
-- source:
--   Stone (1977), Ann. Statist. 5, Corollary 1, p. 598 (necessity direction)

import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting

namespace StoneRegression.Quantile

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- Corollary 1 (necessity half), p. 598: a consistent sequence of (measurable) probability weights
satisfies (1) for some `C ≥ 1`, (3) and (5). For probability weights `|W_{ni}| = W_{ni}`, so `Cond1`,
`Cond3`, `Cond5` (stated with absolute values) are the corollary's three conditions. -/
theorem corollary_1_necessity {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : StoneRegression.Criterion.WeightSeq d) (hW : StoneRegression.Criterion.MeasurableWeights W) (hP : StoneRegression.Criterion.ProbWeights W) (hcons : StoneRegression.Criterion.IsConsistent μ W) :
    (∃ C : ℝ≥0, 1 ≤ C ∧ StoneRegression.Criterion.Cond1 μ W C) ∧ StoneRegression.Criterion.Cond3 μ W ∧ StoneRegression.Criterion.Cond5 μ W := by sorry

end StoneRegression.Quantile
