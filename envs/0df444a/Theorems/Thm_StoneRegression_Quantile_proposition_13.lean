-- Prove2me | Theorems.Thm_StoneRegression_Quantile_proposition_13
-- name    : StoneRegression.Quantile.proposition_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:22:24.74878+00:00
-- url     : https://prove2.me/theorems/007af6ff-5367-4738-9fd1-734b5f3e4828
-- title:
--   Proposition 13, p. 616 — P(L̂ₙ ≥ L − ε) → 1 and P(Ûₙ ≤ U + ε) → 1 for consistent probability weights
-- statement:
--   Let $\{W_n\}$ be a consistent sequence of (jointly Borel) probability weights, let $0<p<1$, and let $Y$ be any real response with $(X,Y),(X_1,Y_1),\dots$ i.i.d. Write $L(X)=L^Y(p\mid X)$, $U(X)=U^Y(p\mid X)$ for the lower and upper conditional quantiles and $\hat L_n(X)$, $\hat U_n(X)$ for their weighted estimates. Then for every $\varepsilon>0$
--   $$\lim_n P\big(\hat L_n(X)\ge L(X)-\varepsilon\big)=1\qquad\text{and}\qquad \lim_n P\big(\hat U_n(X)\le U(X)+\varepsilon\big)=1.$$
--
--   This is the in-probability content of Theorem 3: the estimated lower quantile does not undershoot the true one, and the estimated upper quantile does not overshoot it, by more than any fixed $\varepsilon$ with probability tending to one.
--
--   **Formalization Note.** The response is given by its conditional law, a Markov kernel $\kappa$, which is universally quantified; consistency is a hypothesis on the weights alone and itself quantifies over all responses. Probabilities are evaluated under the law of the i.i.d. pairs.
-- source:
--   Stone (1977), Ann. Statist. 5, Proposition 13, p. 616 (§12)

import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting
import Definitions.Def_StoneRegression_Quantile_Quantiles

namespace StoneRegression.Quantile

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- Proposition 13, p. 616: for a consistent sequence of probability weights, `0 < p < 1` and any
conditional law `κ` of `Y` given `X`, for every `ε > 0`,
`P(L̂ₙ(p|X) ≥ L(p|X) − ε) → 1` and `P(Ûₙ(p|X) ≤ U(p|X) + ε) → 1`. -/
theorem proposition_13 {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : StoneRegression.Criterion.WeightSeq d) (hW : StoneRegression.Criterion.MeasurableWeights W) (hP : StoneRegression.Criterion.ProbWeights W) (hcons : StoneRegression.Criterion.IsConsistent μ W)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ] :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => StoneRegression.Criterion.pairLaw μ κ {ω | lowerQ κ p (ω 0).1 - ε ≤ estLowerQ W n p ω}) atTop (𝓝 1) ∧
      Tendsto (fun n => StoneRegression.Criterion.pairLaw μ κ {ω | estUpperQ W n p ω ≤ upperQ κ p (ω 0).1 + ε}) atTop (𝓝 1) := by sorry

end StoneRegression.Quantile
