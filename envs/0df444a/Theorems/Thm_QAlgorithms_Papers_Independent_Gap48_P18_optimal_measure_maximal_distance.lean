-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_optimal_measure_maximal_distance
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.optimal_measure_maximal_distance
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:42:00.689024+00:00
-- url     : https://prove2.me/theorems/5fef0632-ceb0-46e2-8c3a-baac1ba9a7f9
-- title:
--   Proposition 8
-- statement:
--   Let $A$ be nonempty and closed with finite capacity. Every optimal Borel probability law $\mu_*$ on $A$ satisfies
--
--   $$\bar\rho(\mu_*)=\Omega(A),\qquad D(\rho\|\Omega(A))=\bar C(A)\quad\mu_*\text{-almost everywhere}.$$
--
--   For an optimal finite or countable ensemble, the same average identity holds, and the divergence equality holds for every positive-weight signal. This is the maximal-distance characterization; it does not assert equality at every point of the support.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 39, Proposition 8

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

/-- Proposition 8, arXiv:quant-ph/0510073v2, PDF pp.39,40.
 -/
theorem optimal_measure_maximal_distance {I : Type} [Countable I] [Nonempty I]
    (A : Set (State I)) (hA : A.Nonempty) (hclosed : IsClosed A)
    (hfinite : setChiCapacity A < ⊤) :
    (∀ mu : GeneralizedEnsemble I, OptimalMeasure A mu →
      probabilityAverage mu = optimalAverage A hA ∧
        ∀ᵐ rho ∂(mu : Measure (State I)), stateRelativeEntropyNats rho (optimalAverage A hA) = setChiCapacity A) ∧
    (∀ (w : ℕ → ℝ≥0) (rho : ℕ → State I), HasSum w 1 →
      (∀ n, rho n ∈ A) → measureHolevo (countableLaw w rho) = setChiCapacity A →
      meanCoefficients (countableLaw w rho) = (optimalAverage A hA).coefficients ∧
        ∀ n, 0 < w n → stateRelativeEntropyNats (rho n) (optimalAverage A hA) = setChiCapacity A) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
