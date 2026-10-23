-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P07_isometricCapacity_eq
-- name    : QAlgorithms.Papers.Independent.Gap20.P07.isometricCapacity_eq
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:09:38.097314+00:00
-- url     : https://prove2.me/theorems/750db0b4-35a8-48c4-8698-86bac66b9a46
-- title:
--   Sections 2.8 and 5: isometric encoding suffices
-- statement:
--   Let $T$ be a memoryless CPTP channel between nonzero complex Hilbert spaces. Define $Q_{\rm iso}(T)$ using the channel-fidelity capacity with encoders restricted to $E_n(X)=V_nXV_n^*$ for isometries from the logical space into the physical input block. Decoders remain arbitrary CPTP maps. Then
--   $$Q_{\rm iso}(T)=Q(T).$$
--   This restricts the encoding apparatus alone and makes no claim about homomorphic decoding.
-- source:
--   Tema Con Variazioni: Quantum Channel Capacity, arXiv:quant-ph/0311037v1, PDF p. 7, Sections 2.8 and 5: isometric encoding suffices

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P07

noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal NNReal Matrix ComplexOrder ComplexConjugate

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Gap20.P07

open QAlgorithms

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel traceSize rankOne tensorApply)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation isometryCoeff conjugateKernel)

open QAlgorithms.Papers.Independent.Claimed50.P35
  (stabilizedTraceClassNorm traceClassTensorMap traceClassChannelPower
   transpose transposeBound TraceLinear tracePair MeasurePrepare)

open QAlgorithms.Papers.Independent.Gap48.P29 (fe FiniteCPMap)

/-- PDF pp.7,20--22: isometric encoding suffices, with arbitrary CPTP decoding. -/
theorem isometricCapacity_eq {I J : Type} [Nonempty I] [Nonempty J]
    (T : Operation I J) (hT : IsTraceClassChannel T) :
    isometricCapacity T = qubitReferenceCapacity T := by sorry

end QAlgorithms.Papers.Independent.Gap20.P07

end
