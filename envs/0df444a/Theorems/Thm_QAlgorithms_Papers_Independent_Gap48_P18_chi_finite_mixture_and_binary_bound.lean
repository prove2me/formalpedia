-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_chi_finite_mixture_and_binary_bound
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.chi_finite_mixture_and_binary_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:33:55.750079+00:00
-- url     : https://prove2.me/theorems/b2878e16-91e2-4ac4-a9b3-870c2082760f
-- title:
--   Lemma 1
-- statement:
--   Let $\mu_1,\ldots,\mu_m$ be Borel probability measures on the trace-norm state space of a nonzero separable complex Hilbert space, with barycenters $\bar\rho_k$, and let $\lambda_k\ge0$ sum to one. With natural logarithms and extended nonnegative integrals,
--
--   $$\chi\left(\sum_k\lambda_k\mu_k\right)=\sum_k\lambda_k\chi(\mu_k)+\chi(\{\lambda_k,\bar\rho_k\}).$$
--
--   For two such measures and $t\in[0,1]$,
--
--   $$\chi(t\mu+(1-t)\nu)\ge t\chi(\mu)+(1-t)\chi(\nu)+\tfrac12t(1-t)\|\bar\rho_\nu-\bar\rho_\mu\|_1^2.$$
--
--   Zero weights contribute zero, including at infinite entropy. This identity separates within-ensemble and between-ensemble information.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 6, Lemma 1

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P18

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology Matrix.Norms.L2Operator

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState traceSize traceClosure IsTraceClassChannel productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble HasFiniteSupport HasAverage averageCoefficients
   extendedEntropyNats extendedRelativeEntropyNats
   finiteEnsembleCapacity pureStates)

open QAlgorithms.Papers.Independent.Frontier18.P01 (traceFirst traceSecond)

namespace QAlgorithms.Papers.Independent.Gap48.P18

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 1, arXiv:quant-ph/0510073v2, PDF pp.6.
NNReal weights with t≤1 encode exactly [0,1]; finite-mixture measures are constructed explicitly. -/
theorem chi_finite_mixture_and_binary_bound {I : Type} [Countable I] [Nonempty I] :
    (∀ (m : ℕ) (w : Fin m → ℝ≥0) (mu : Fin m → GeneralizedEnsemble I),
      (∑ k, w k) = 1 →
      measureHolevo (∑ k, (w k : ℝ≥0∞) • (mu k : Measure (State I))) =
        (∑ k, (w k : ℝ≥0∞) * measureHolevo (mu k : Measure (State I))) +
          measureHolevo (∑ k, (w k : ℝ≥0∞) • Measure.dirac (probabilityAverage (mu k)))) ∧
    (∀ (mu nu : GeneralizedEnsemble I) (t : ℝ≥0), t ≤ 1 →
      (t : ℝ≥0∞) * measureHolevo (mu : Measure (State I)) +
          ((1 - t : ℝ≥0) : ℝ≥0∞) * measureHolevo (nu : Measure (State I)) +
          ((t * (1 - t) / 2 : ℝ≥0) : ℝ≥0∞) *
            distanceSquared (probabilityAverage nu) (probabilityAverage mu) ≤
        measureHolevo ((t : ℝ≥0∞) • (mu : Measure (State I)) +
          ((1 - t : ℝ≥0) : ℝ≥0∞) • (nu : Measure (State I)))) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
