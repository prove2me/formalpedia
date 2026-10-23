-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_finite_ensemble_capacity_deficit
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.finite_ensemble_capacity_deficit
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:38:30.960719+00:00
-- url     : https://prove2.me/theorems/d8f089d6-7c10-417d-9851-f425deaf9649
-- title:
--   Corollary 4
-- statement:
--   Let $A$ be nonempty with finite capacity and let $\mu$ be a finite ensemble of states in $A$, with average $\bar\rho$. Then $\chi(\mu)$ and $D(\bar\rho\|\Omega(A))$ are finite, and
--
--   $$\bar C(A)-\chi(\mu)\ge D(\bar\rho\|\Omega(A))\ge\tfrac12\|\bar\rho-\Omega(A)\|_1^2.$$
--
--   No finite-entropy assumption on the average is required. The deficit controls its distance to the optimal average.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 27, Corollary 4

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

/-- Corollary 4, arXiv:quant-ph/0510073v2, PDF pp.27.
 -/
theorem finite_ensemble_capacity_deficit {I : Type} [Countable I] [Nonempty I]
    (A : Set (State I)) (hA : A.Nonempty) (hfinite : setChiCapacity A < ⊤)
    (mu : GeneralizedEnsemble I) (hmu : FiniteEnsembleOn mu A) :
    measureHolevo (mu : Measure (State I)) < ⊤ ∧
      stateRelativeEntropyNats (probabilityAverage mu) (optimalAverage A hA) < ⊤ ∧
      stateRelativeEntropyNats (probabilityAverage mu) (optimalAverage A hA) ≤
        ENNReal.ofReal ((setChiCapacity A).toReal - (measureHolevo (mu : Measure (State I))).toReal) ∧
      distanceSquared (probabilityAverage mu) (optimalAverage A hA) / 2 ≤
        stateRelativeEntropyNats (probabilityAverage mu) (optimalAverage A hA) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
