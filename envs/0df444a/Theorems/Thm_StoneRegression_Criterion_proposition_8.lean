-- Prove2me | Theorems.Thm_StoneRegression_Criterion_proposition_8
-- name    : StoneRegression.Criterion.proposition_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:44:11.458342+00:00
-- url     : https://prove2.me/theorems/3df78f70-7fb0-4208-8a31-6dd332daa18d
-- title:
--   Proposition 8, p. 610 — $\sum_i W_{ni}(X)Y_i\to0$ in probability for normal $Y_i$ forces $\sum_i W_{ni}^2(X)\to0$
-- statement:
--   Let $X, X_1, X_2,\dots$ be i.i.d. $\mathbb R^d$-valued with law $\mu$, and let $Y_1, Y_2,\dots$ be independent standard normal real random variables, independent of $(X, X_1, X_2,\dots)$. Let $\{W_n\}$ be a sequence of Borel weights such that
--   $$\sum_i W_{ni}(X)\,Y_i \to 0\quad\text{in probability.}$$
--   Then
--   $$\sum_i W_{ni}^2(X)\to 0\quad\text{in probability.}$$
--
--   Since $\max_i |W_{ni}(X)|^2\le\sum_i W_{ni}^2(X)$, this is the step from consistency to condition (5) in the necessity half of Theorem 1.
--
--   **Formalization Note.** The variables $X, X_1, \dots$ and $Y_1, Y_2,\dots$ are realized as the coordinates of the product law of i.i.d. pairs $(X_i, Y_i)$ with $X_i\sim\mu$ and $Y_i\sim N(0,1)$ independent of $X_i$ (the kernel $\kappa\equiv N(0,1)$). This also produces a normal variable paired with $X$ itself, which the statement does not use. Since the joint law of $(X, X_1, X_2,\dots, Y_1, Y_2,\dots)$ is the same for every such sequence $\{Y_i\}$ and convergence in probability depends only on the joint law, the paper's "there is a sequence $\{Y_i\}$" is captured exactly. Weights are assumed jointly Borel (standing assumption).
-- source:
--   Stone (1977), Ann. Statist. 5, Proposition 8, p. 610

import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace StoneRegression.Criterion

/-- Proposition 8 (Stone 1977, p. 610). Let `Y₁, Y₂, …` be i.i.d. standard normal and independent of
`(X, X₁, X₂, …)`; these are the response coordinates of `pairLaw μ (Kernel.const _ (gaussianReal 0 1))`
(the response paired with `X` itself is also present there, and unused). If `∑ᵢ W_{ni}(X) Yᵢ → 0` in
probability, then `∑ᵢ W²_{ni}(X) → 0` in probability. -/
theorem proposition_8 {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : WeightSeq d) (hW : MeasurableWeights W)
    (hY : TendstoInMeasure (pairLaw μ (Kernel.const (EuclideanSpace ℝ (Fin d)) (gaussianReal 0 1)))
      (fun n ω => estimate W n ω) atTop (fun _ => 0)) :
    TendstoInMeasure (xLaw μ) (fun n ω => ∑ i : Fin n, wAt W n ω i ^ 2) atTop (fun _ => 0) := by sorry

end StoneRegression.Criterion
