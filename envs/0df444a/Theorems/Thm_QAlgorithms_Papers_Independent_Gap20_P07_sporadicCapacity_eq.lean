-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P07_sporadicCapacity_eq
-- name    : QAlgorithms.Papers.Independent.Gap20.P07.sporadicCapacity_eq
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:02:44.842619+00:00
-- url     : https://prove2.me/theorems/72f2fe87-1209-44f6-a61c-0bcab16aefcd
-- title:
--   Sections 2.2 and 7.3: sporadic capacity equals Q
-- statement:
--   Let $T$ be a memoryless CPTP channel between nonzero complex Hilbert spaces. A positive rate $R$ is sporadic if there are positive block sequences $n_\nu\to\infty,m_\nu$ whose ratio has limsup $R$ and whose optimal full-cb coding errors tend to zero. Let $Q_{\rm spor}(T)$ be the extended nonnegative supremum of such rates. Then
--   $$Q_{\rm spor}(T)=Q(T).$$
--   This is equality of suprema. The extension argument achieves every strict subrate, and does not assert that the sporadic endpoint satisfies every sequence allowed by Definition 2.1.
-- source:
--   Tema Con Variazioni: Quantum Channel Capacity, arXiv:quant-ph/0311037v1, PDF p. 4, Sections 2.2 and 7.3: sporadic capacity equals Q

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

/-- PDF pp.4,25--29: equality of suprema; no false endpoint assertion. -/
theorem sporadicCapacity_eq {I J : Type} [Nonempty I] [Nonempty J]
    (T : Operation I J) (hT : IsTraceClassChannel T) :
    sporadicCapacity T = qubitReferenceCapacity T := by sorry

end QAlgorithms.Papers.Independent.Gap20.P07

end
