-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P43_sufficientStatisticIffRandomization
-- name    : QAlgorithms.Papers.Independent.Next46.P43.sufficientStatisticIffRandomization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:41:27.760708+00:00
-- url     : https://prove2.me/theorems/760c343a-b6f1-4bd5-99a9-f9bebc94e2e3
-- title:
--   Proposition 2: statistic sufficiency equals randomization equivalence
-- statement:
--   Let $\mathcal P=(P_\theta)_{\theta\in\Theta}$ be a nonempty dominated family of probabilities on $(X,\mathcal A)$, with a sigma-finite dominating measure. Let $T:(X,\mathcal A)\to(Y,\mathcal B)$ be measurable and let $P_\theta^T=T_*P_\theta$ be its image probabilities. Then
--
--   $$
--   T\text{ is sufficient for }\mathcal P
--   \quad\Longleftrightarrow\quad
--   (X,\mathcal A,\mathcal P)\text{ and }(Y,\mathcal B,\mathcal P^T)\text{ are stochastically equivalent}.
--   $$
--
--   Sufficiency refers to the sigma-algebra $T^{-1}\mathcal B$. Stochastic equivalence is implemented by family-preserving normal positive unital $L^\infty$ operators. A single reverse operator works for every $\theta$; no standard-Borel assumption or stochastic-kernel representation is imposed. This identifies sufficient statistics with reversible statistical randomizations.
-- source:
--   Sufficiency in quantum statistical inference, arXiv:math-ph/0412093v1, PDF p. 11, Proposition 2: statistic sufficiency equals randomization equivalence

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P43

noncomputable section

open MeasureTheory Filter

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P43

open QAlgorithms.Papers.Independent.Dependency50.P33
  (IsTraceClass IsDensity State tensorApply productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (homogeneousEntropy generalizedRelativeEntropy traceFirst traceSecond)

/-- Proposition 2, PDF p.11. The image family is the actual pushforward of the
probabilities under the measurable statistic. One reverse normal Markov map
works for the whole family, without a standard-Borel or kernel assumption. -/
theorem sufficientStatisticIffRandomization
    {X Y Theta : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
    [Nonempty Theta] (P : Theta → Measure X)
    (hProb : ∀ theta, IsProbabilityMeasure (P theta))
    (mu : Measure X) [SigmaFinite mu] (hDom : ∀ theta, P theta ≪ mu)
    (T : X → Y) (hT : Measurable T) :
    SufficientSigmaAlgebra P (MeasurableSpace.comap T mY) ↔
      StochasticallyEquivalent mX mY P (fun theta => (P theta).map T) := by sorry

end QAlgorithms.Papers.Independent.Next46.P43

end
