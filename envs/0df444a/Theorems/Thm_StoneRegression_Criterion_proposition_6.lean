-- Prove2me | Theorems.Thm_StoneRegression_Criterion_proposition_6
-- name    : StoneRegression.Criterion.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:44:01.984159+00:00
-- url     : https://prove2.me/theorems/05fb1a35-9e4d-4c99-a274-fe1901596a02
-- title:
--   Proposition 6, pp. 609–610 — nonnegative weights that reproduce bounded continuous $f$ satisfy (3)
-- statement:
--   Let $X, X_1, X_2,\dots$ be i.i.d. $\mathbb R^d$-valued with law $\mu$, and let $\{W_n\}$ be a sequence of nonnegative Borel weights such that, for every bounded continuous function $f$ on $\mathbb R^d$,
--   $$\sum_i W_{ni}(X)f(X_i) \to f(X) \quad\text{in probability.}$$
--   Then $\{W_n\}$ satisfies condition (3):
--   $$\sum_i W_{ni}(X)\,I_{\{\|X_i - X\|>a\}}\to 0 \quad\text{in probability, for every } a>0 .$$
--
--   This is the step from consistency to the localization condition (3) in the necessity half of Theorem 1 (applied to responses $Y = f(X)$).
--
--   **Formalization Note.** Convergence in probability is Mathlib's convergence in measure under the product law of $(X, X_1, X_2,\dots)$; bounded continuous functions are Mathlib's `BoundedContinuousFunction`. Weights are assumed jointly Borel (standing assumption).
-- source:
--   Stone (1977), Ann. Statist. 5, Proposition 6, pp. 609–610

import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace StoneRegression.Criterion

/-- Proposition 6 (Stone 1977, pp. 609–610). Nonnegative weights such that `∑ᵢ W_{ni}(X) f(Xᵢ) → f(X)` in
probability for every bounded continuous `f` on `ℝᵈ` satisfy (3). -/
theorem proposition_6 {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : WeightSeq d) (hW : MeasurableWeights W) (hnn : Nonneg W)
    (hconv : ∀ f : EuclideanSpace ℝ (Fin d) →ᵇ ℝ, TendstoInMeasure (xLaw μ)
      (fun n ω => ∑ i : Fin n, wAt W n ω i * f (ω (i.val + 1))) atTop (fun ω => f (ω 0))) :
    Cond3 μ W := by sorry

end StoneRegression.Criterion
