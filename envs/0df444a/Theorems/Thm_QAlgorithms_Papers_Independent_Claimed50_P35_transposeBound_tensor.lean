-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P35_transposeBound_tensor
-- name    : QAlgorithms.Papers.Independent.Claimed50.P35.transposeBound_tensor
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:28:38.185722+00:00
-- url     : https://prove2.me/theorems/04fecae2-2ce4-4368-92a6-4f9e295b1b56
-- title:
--   II.B, Eq.(2.10): tensor additivity
-- statement:
--   For any two full trace-class quantum channels $S$ and $T$ on nonzero completed complex Hilbert spaces, their transpose bounds are exactly additive:
--
--   $$Q_\Theta(S\otimes T)=Q_\Theta(S)+Q_\Theta(T).$$
--
--   Here $Q_\Theta(\Phi)=\log_2\|\Phi\circ\Theta\|_\diamond$, with the full completely bounded trace norm and extended nonnegative values. The tensor map retains off-diagonal blocks of entangled inputs. This identifies a parallel-composition law for the capacity bound.
-- source:
--   Evaluating Capacities of Bosonic Gaussian Channels, arXiv:quant-ph/9912067v1, PDF p. 4, II.B, Eq.(2.10): tensor additivity

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

/-- II.B, (2.10), p.4: exact tensor additivity, including infinity. -/
theorem transposeBound_tensor {I J K L : Type}
    [Nonempty I] [Nonempty J] [Nonempty K] [Nonempty L]
    (S : Operation I J) (T : Operation K L)
    (hS : IsTraceClassChannel S) (hT : IsTraceClassChannel T) :
    transposeBound (traceClassTensorMap S T) = transposeBound S + transposeBound T := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P35

end
