-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_layer_capacity_and_optimal_pure_measure
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.layer_capacity_and_optimal_pure_measure
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:45:06.023607+00:00
-- url     : https://prove2.me/theorems/401f03a7-65fd-4aa8-97bc-c10b8d8ffa7e
-- title:
--   Proposition 6b
-- statement:
--   For a density state $\sigma$, retain a chosen eigenbasis in the definition of its layer $L(\sigma)$. Then, including infinite values,
--
--   $$\bar C(L(\sigma))=H(\sigma).$$
--
--   The layer is regular exactly when $H(\sigma)<\infty$. In that case $\Omega(L(\sigma))=\sigma$, and there is an optimal law with barycenter $\sigma$ concentrated on pure states in the layer. This gives the capacity and optimal-measure structure of a fixed-diagonal set.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 51, Proposition 6b

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

/-- Proposition 6b, arXiv:quant-ph/0510073v2, PDF pp.51,52.
 -/
theorem layer_capacity_and_optimal_pure_measure {I : Type} [Countable I] [Nonempty I]
    (sigma : State I) (hdiag : Diagonal sigma) :
    setChiCapacity (layer sigma) = stateEntropyNats sigma ∧
      (ChiRegular (layer sigma) ↔ stateEntropyNats sigma < ⊤) ∧
      (stateEntropyNats sigma < ⊤ →
        (∀ hL : (layer sigma).Nonempty, optimalAverage (layer sigma) hL = sigma) ∧
        ∃ mu : GeneralizedEnsemble I, OptimalMeasure (layer sigma) mu ∧
          probabilityAverage mu = sigma ∧
          MeasureConcentratedOn (mu : Measure (State I)) (layer sigma ∩ pureStates I)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
