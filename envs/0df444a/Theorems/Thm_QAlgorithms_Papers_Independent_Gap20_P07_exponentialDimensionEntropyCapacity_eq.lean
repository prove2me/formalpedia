-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P07_exponentialDimensionEntropyCapacity_eq
-- name    : QAlgorithms.Papers.Independent.Gap20.P07.exponentialDimensionEntropyCapacity_eq
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:05:30.131991+00:00
-- url     : https://prove2.me/theorems/456fe72e-01b9-4a3c-b6d5-1e15b854b99b
-- title:
--   Sections 2.6 and 4.4: entropy capacity for exponentially bounded source dimensions
-- statement:
--   Let $T$ be a memoryless CPTP channel between nonzero complex Hilbert spaces. Consider finite nonzero block sources $\rho_n$ transmitted by CPTP encoders and decoders with squared entanglement fidelity tending to one. Require each source to have some constant $\tau>0$ such that $\dim H_n\le\tau^n$ for every positive $n$. Compute its bit-entropy rate using a limsup, and take the extended nonnegative supremum over sources and positive rates. Then
--   $$Q_{\rm expdim}(T)=Q(T).$$
--   The growth constant varies with the source, and entropy rates need not converge. This gives the second source restriction under which entropy capacity agrees with quantum capacity.
-- source:
--   Tema Con Variazioni: Quantum Channel Capacity, arXiv:quant-ph/0311037v1, PDF p. 6, Sections 2.6 and 4.4: entropy capacity for exponentially bounded source dimensions

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

/-- PDF pp.6,19: each exponentially bounded source has its own tau; the entropy
rate is a limsup and need not converge. -/
theorem exponentialDimensionEntropyCapacity_eq {I J : Type} [Nonempty I] [Nonempty J]
    (T : Operation I J) (hT : IsTraceClassChannel T) :
    sourceEntropyCapacity T QuantumSource.ExponentialDimension = qubitReferenceCapacity T := by sorry

end QAlgorithms.Papers.Independent.Gap20.P07

end
