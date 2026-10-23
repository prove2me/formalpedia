-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_holevoCapacity_inputDimensionBound
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.holevoCapacity_inputDimensionBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:04:43.783438+00:00
-- url     : https://prove2.me/theorems/956cdcdb-97f2-4b8b-b681-a7360b6c02a6
-- title:
--   Unnumbered result (20): finite-dimensional Holevo capacity bound
-- statement:
--   All physical Hilbert spaces are nonzero complex separable Hilbert spaces, with finite dimensions included. States are positive trace-class operators of trace one, channels are completely positive and trace preserving on the entire trace class, and logarithms are natural. Inner products are conjugate-linear in the first argument. Let both input and output spaces have positive finite dimensions. Define the single-letter Holevo capacity by $\bar C(\Phi)=\sup_e\chi(\Phi(e))$, over discrete input ensembles. Then
--
--   $$\bar C(\Phi)\le\ln\dim H_A.$$
--
--   This result bounds the single-letter classical information by the input dimension.
-- source:
--   Reversibility conditions for quantum channels and their applications, arXiv:1203.0262v3, PDF p. 21, Unnumbered result (20): finite-dimensional Holevo capacity bound

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P45

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Gap48.P45

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel traceSize traceClosure rankOne productCoeff tensorApply)

open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel Complementary traceFirst traceSecond)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble averageCoefficients extendedEntropyNats extendedRelativeEntropyNats ensembleHolevo pureStates finiteEnsembleCapacity)

open QAlgorithms.Papers.Independent.Frontier18.P18
  (operatorCoeff boundedOperator conjugateCoeff ReversibleOn IsometricallyEquivalent
   IsParsevalFrame IsKrausRepresentation)

open QAlgorithms.Papers.Independent.Claimed50.P16 (tensorRankLE)

open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot)

open QAlgorithms.Papers.Independent.Next46.P42 (minimumOutputEntropy)

/-- Equation (20), PDF p.21: finite-dimensional single-letter capacity bound,
in nats. Both physical spaces are positive finite-dimensional. -/
theorem holevoCapacity_inputDimensionBound
    {I J : Type} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    (Phi : Channel I J) :
    (finiteEnsembleCapacity Phi.val Set.univ) ≤ ENNReal.ofReal (Real.log (Fintype.card I : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45

end
