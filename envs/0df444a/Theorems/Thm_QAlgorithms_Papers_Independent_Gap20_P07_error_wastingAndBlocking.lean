-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P07_error_wastingAndBlocking
-- name    : QAlgorithms.Papers.Independent.Gap20.P07.error_wastingAndBlocking
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:26:40.308823+00:00
-- url     : https://prove2.me/theorems/208f8f35-2cfc-4a54-b19b-c279c01ca135
-- title:
--   Sections 7.1–7.2 / (94),(101): resource wasting and tensor blocking
-- statement:
--   Let $T,S$ be arbitrary CPTP channels on nonzero complex Hilbert spaces and let $\Delta(n,m)$ be their computed full-cb simulation error for positive integers $n,m$. Then
--   $$\Delta(n+1,m)\le\Delta(n,m)\le\Delta(n,m+1),$$
--   and for all positive $n_1,n_2,m_1,m_2$,
--   $$\Delta(n_1+n_2,m_1+m_2)\le\Delta(n_1,m_1)+\Delta(n_2,m_2).$$
--   These are consequences of wasting resources and tensor blocking, not hypotheses imposed on the physical channel. The reference $S$ may be noisy.
-- source:
--   Tema Con Variazioni: Quantum Channel Capacity, arXiv:quant-ph/0311037v1, PDF p. 26, Sections 7.1–7.2 / (94),(101): resource wasting and tensor blocking

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

/-- PDF pp.26--27, (94),(101): resource wasting and blocking are conclusions
about the computed physical-channel error, including noisy references. -/
theorem error_wastingAndBlocking {I J K L : Type}
    [Nonempty I] [Nonempty J] [Nonempty K] [Nonempty L]
    (T : Operation I J) (S : Operation K L)
    (hT : IsTraceClassChannel T) (hS : IsTraceClassChannel S) :
    ErrorMonotone (blockError T S) ∧ ErrorSubadditive (blockError T S) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P07

end
