-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P07_partialTranspose_upperBound
-- name    : QAlgorithms.Papers.Independent.Gap20.P07.partialTranspose_upperBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:15:51.844848+00:00
-- url     : https://prove2.me/theorems/a8f6b8d5-8d90-403b-ac08-51d0c16d605f
-- title:
--   Section 3.3 / (25): partial transposition upper bound
-- statement:
--   Let $T$ be a CPTP channel on nonzero complex Hilbert spaces, and let $0<\epsilon<1$. With $Q_\epsilon$ defined by eventual full-cb error at most $\epsilon$ and $\Theta$ the fixed-basis input transpose,
--   $$Q(T)\le Q_\epsilon(T)\le Q_\Theta(T):=\log_2\|T\Theta\|_{\rm cb}.$$
--   The logarithmic bound is extended-valued when the norm is infinite. The basis choice does not affect its value. The proof needs only a fixed error strictly below one.
-- source:
--   Tema Con Variazioni: Quantum Channel Capacity, arXiv:quant-ph/0311037v1, PDF p. 10, Section 3.3 / (25): partial transposition upper bound

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

/-- PDF pp.10--11, (25)--(27): fixed full-cb epsilon<1 suffices; an infinite
transpose norm gives an infinite upper bound, never a real-supremum default. -/
theorem partialTranspose_upperBound {I J : Type} [Nonempty I] [Nonempty J]
    (T : Operation I J) (hT : IsTraceClassChannel T)
    (epsilon : ℝ) (heps : 0 < epsilon) (heps1 : epsilon < 1) :
    qubitReferenceCapacity T ≤ finiteErrorCapacity T epsilon ∧
    finiteErrorCapacity T epsilon ≤ transposeBound T := by sorry

end QAlgorithms.Papers.Independent.Gap20.P07

end
