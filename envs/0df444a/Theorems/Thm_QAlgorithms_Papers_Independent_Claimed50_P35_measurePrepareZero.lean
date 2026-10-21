-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P35_measurePrepareZero
-- name    : QAlgorithms.Papers.Independent.Claimed50.P35.measurePrepareZero
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:32:05.256238+00:00
-- url     : https://prove2.me/theorems/09a6e616-1f4b-4216-85b4-4e634806e736
-- title:
--   II.B: measure-and-prepare zero bound
-- statement:
--   Suppose a full trace-class CPTP channel $T$ factors into a measurement followed by preparation of a normalized output state depending on the outcome. The measurement is an arbitrary POVM, with its countably additive probability law on a measurable outcome space; continuous outcomes are allowed. Then
--
--   $$Q_\Theta(T)=0.$$
--
--   The preparation integrals are actual density-valued mixtures, specified by integrable coefficients. This supplies the source's separable-channel instance of the zero transpose bound.
-- source:
--   Evaluating Capacities of Bosonic Gaussian Channels, arXiv:quant-ph/9912067v1, PDF p. 4, II.B: measure-and-prepare zero bound

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P35

noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal NNReal BigOperators

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Claimed50.P35

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39
  (displacementMatrix attenuatorMatrix amplifierMatrix thermalMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation conjugateKernel composeKernel partialRight isometryCoeff identityCoeff)

open QAlgorithms.Papers.Independent.Frontier30.P21 (bosonicEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

/-- II.B, p.4: general measurement/preparation factorization. -/
theorem measurePrepareZero {I J : Type} [Nonempty I] [Nonempty J]
    (T : Operation I J) (hT : IsTraceClassChannel T) (hMP : MeasurePrepare T) :
    transposeBound T = 0 := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P35

end
