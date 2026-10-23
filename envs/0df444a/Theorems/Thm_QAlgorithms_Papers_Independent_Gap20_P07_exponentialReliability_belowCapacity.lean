-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P07_exponentialReliability_belowCapacity
-- name    : QAlgorithms.Papers.Independent.Gap20.P07.exponentialReliability_belowCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:07:13.542925+00:00
-- url     : https://prove2.me/theorems/9946b9fb-5b0f-49a3-b8c7-2a8a25f8f800
-- title:
--   Sections 2.7 and 7.3: positive exponential reliability below capacity
-- statement:
--   Let $T$ be a memoryless CPTP channel between nonzero complex Hilbert spaces, and let $0<R<Q(T)$. There are constants $a,C>0$ and CPTP codes for every positive block length $n$, transmitting exactly $\lfloor nR\rfloor$ logical qubits, such that
--   $$\|D_nT^{\otimes n}E_n-\mathrm{id}_{2^{\lfloor nR\rfloor}}\|_{\rm cb}\le Ce^{-an}\quad\text{eventually}.$$
--   The exponent may depend on $T$ and $R$. For every channel, including those of zero capacity, the extended supremum of positive rates with such reliability equals $Q(T)$. No prescribed exponent or reliability at the capacity endpoint is asserted.
-- source:
--   Tema Con Variazioni: Quantum Channel Capacity, arXiv:quant-ph/0311037v1, PDF p. 6, Sections 2.7 and 7.3: positive exponential reliability below capacity

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

/-- PDF pp.6,29: the positive exponent may depend on both channel and rate. -/
theorem exponentialReliability_belowCapacity {I J : Type} [Nonempty I] [Nonempty J]
    (T : Operation I J) (hT : IsTraceClassChannel T) :
    exponentialCapacity T = qubitReferenceCapacity T ∧
    ∀ R : ℝ, 0 < R → ENNReal.ofReal R < qubitReferenceCapacity T → ExponentialReliable T R := by sorry

end QAlgorithms.Papers.Independent.Gap20.P07

end
