-- Prove2me | Theorems.Thm_StoneRegression_Criterion_proposition_7
-- name    : StoneRegression.Criterion.proposition_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:57.005412+00:00
-- url     : https://prove2.me/theorems/4fd19b25-7717-41dc-93d2-eb340d9ad4cc
-- title:
--   Proposition 7, p. 610 — finite limsup of $E\sum_i W_{ni}(X)f(X_i)$ for every integrable $f$ gives a uniform $C$
-- statement:
--   Let $X, X_1, X_2,\dots$ be i.i.d. $\mathbb R^d$-valued with law $\mu$, and let $\{W_n\}$ be a sequence of nonnegative Borel weights such that, for every nonnegative Borel function $f$ on $\mathbb R^d$ with $Ef(X)<\infty$,
--   $$\limsup_{n\to\infty} E\sum_i W_{ni}(X)f(X_i) < \infty .$$
--   Then there are a positive integer $n_0$ and a positive constant $C$ such that, for every nonnegative Borel function $f$ on $\mathbb R^d$,
--   $$E\sum_i W_{ni}(X)f(X_i) \le C\,Ef(X)\qquad\text{for all } n\ge n_0 .$$
--
--   The constants $n_0$ and $C$ do not depend on $f$. This uniform-boundedness statement is the step from consistency to condition (1) in the necessity half of Theorem 1.
--
--   **Formalization Note.** Expectations and the $\limsup$ are taken in $[0,\infty]$, so "$<\infty$" is a genuine finiteness assumption. The order of quantifiers is $\exists n_0\,\exists C\,\forall f\,\forall n\ge n_0$. Weights are assumed jointly Borel (standing assumption).
-- source:
--   Stone (1977), Ann. Statist. 5, Proposition 7, p. 610

import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace StoneRegression.Criterion

/-- Proposition 7 (Stone 1977, p. 610). If the weights are nonnegative and
`limsup_n E ∑ᵢ W_{ni}(X) f(Xᵢ) < ∞` for every nonnegative Borel `f` with `Ef(X) < ∞`, then there are a
positive integer `n₀` and a positive constant `C` such that, for every nonnegative Borel `f`,
`E ∑ᵢ W_{ni}(X) f(Xᵢ) ≤ C Ef(X)` for all `n ≥ n₀`. The `n₀` and `C` are chosen before `f`. -/
theorem proposition_7 {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : WeightSeq d) (hW : MeasurableWeights W) (hnn : Nonneg W)
    (hbdd : ∀ f : EuclideanSpace ℝ (Fin d) → ℝ≥0, Measurable f → ∫⁻ x, f x ∂μ < ∞ →
      limsup (fun n => ∫⁻ ω, ∑ i : Fin n,
        ENNReal.ofReal (wAt W n ω i) * (f (ω (i.val + 1)) : ℝ≥0∞) ∂(xLaw μ)) atTop < ∞) :
    ∃ n₀ : ℕ, 0 < n₀ ∧ ∃ C : ℝ≥0, 0 < C ∧
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ≥0, Measurable f → ∀ n, n₀ ≤ n →
        ∫⁻ ω, ∑ i : Fin n, ENNReal.ofReal (wAt W n ω i) * (f (ω (i.val + 1)) : ℝ≥0∞) ∂(xLaw μ) ≤
          C * ∫⁻ x, f x ∂μ := by sorry

end StoneRegression.Criterion
