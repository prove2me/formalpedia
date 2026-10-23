-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_nonregular_optimal_measure_examples
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.nonregular_optimal_measure_examples
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:48:16.869867+00:00
-- url     : https://prove2.me/theorems/167f3af9-3db1-4d94-a6df-bdad04b9efff
-- title:
--   Remark 8
-- statement:
--   On an infinite-dimensional separable Hilbert space there are nonregular sets of finite capacity without optimal measures, including a convergent sequence of states of finite capacity. There are also nonregular finite-capacity sets with optimal measures. In particular,
--
--   $$\exists A:\ \bar C(A)<\infty,\quad A\text{ nonregular},\quad\exists\mu_*\text{ optimal on }A.$$
--
--   Regularity is therefore a sufficient condition in Theorem 3, but is not necessary.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 42, Remark 8

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

/-- Remark 8, arXiv:quant-ph/0510073v2, PDF pp.42.
 -/
theorem nonregular_optimal_measure_examples {I : Type} [Countable I] [Infinite I] :
    (∃ A : Set (State I), A.Nonempty ∧ setChiCapacity A < ⊤ ∧ ¬ ChiRegular A ∧
      ¬ ∃ mu, OptimalMeasure A mu) ∧
    (∃ (seq : ℕ → State I) (rho : State I),
      Tendsto seq atTop (𝓝 rho) ∧ rho ∈ Set.range seq ∧ setChiCapacity (Set.range seq) < ⊤ ∧
        ¬ ∃ mu, OptimalMeasure (Set.range seq) mu) ∧
    (∃ A : Set (State I), A.Nonempty ∧ setChiCapacity A < ⊤ ∧ ¬ ChiRegular A ∧
      ∃ mu, OptimalMeasure A mu) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
