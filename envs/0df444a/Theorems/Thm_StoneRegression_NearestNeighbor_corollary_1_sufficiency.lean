-- Prove2me | Theorems.Thm_StoneRegression_NearestNeighbor_corollary_1_sufficiency
-- name    : StoneRegression.NearestNeighbor.corollary_1_sufficiency
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:20:30.561924+00:00
-- url     : https://prove2.me/theorems/4545a285-e45d-43a6-8c89-42d12eeef836
-- title:
--   Corollary 1, p. 598 (sufficiency) — probability weights satisfying (1), (3) and (5) are consistent
-- statement:
--   Let $\{W_n\}$ be a sequence of probability weights for an $\mathbb R^d$-valued i.i.d. sequence $X, X_1, X_2, \dots$ with law $\mu$. Suppose that
--
--   1. there is a $C \ge 1$ such that, for every nonnegative Borel function $f$ on $\mathbb R^d$,
--   $$E \sum_i W_{ni}(X) f(X_i) \le C\, E f(X) \qquad \text{for all } n \ge 1;$$
--   2. $\sum_i W_{ni}(X)\, I_{\{\|X_i - X\| > a\}} \to 0$ in probability for every $a > 0$;
--   3. $\max_i W_{ni}(X) \to 0$ in probability.
--
--   Then $\{W_n\}$ is consistent: for every joint law of $(X,Y)$ with this $X$-marginal and every $r \ge 1$ with $E|Y|^r<\infty$, $E|\sum_i W_{ni}(X) Y_i - E(Y\mid X)|^r \to 0$.
--
--   This is the sufficiency half of Corollary 1, the form of Stone's consistency criterion (Theorem 1) for probability weights, where conditions (2) and (4) hold automatically. It is the route by which Theorem 2 is proved.
--
--   **Formalization Note** The weights are assumed jointly Borel. For probability weights $|W_{ni}| = W_{ni}$, so the conditions are stated with the absolute values of the general conditions (1), (3), (5). The necessity half of Corollary 1 is a milestone of mission III of this series; both halves are special cases of Theorem 1 (mission I).
-- source:
--   Stone (1977), Ann. Statist. 5, Corollary 1, p. 598 (sufficiency direction)

import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting

namespace StoneRegression.NearestNeighbor

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

theorem corollary_1_sufficiency {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : StoneRegression.Criterion.WeightSeq d) (hWm : StoneRegression.Criterion.MeasurableWeights W) (hW : StoneRegression.Criterion.ProbWeights W)
    (h1 : ∃ C : ℝ≥0, 1 ≤ C ∧ StoneRegression.Criterion.Cond1 μ W C) (h3 : StoneRegression.Criterion.Cond3 μ W) (h5 : StoneRegression.Criterion.Cond5 μ W) :
    StoneRegression.Criterion.IsConsistent μ W := by sorry

end StoneRegression.NearestNeighbor
