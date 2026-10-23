-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P07_forwardAssistance_useless
-- name    : QAlgorithms.Papers.Independent.Gap20.P07.forwardAssistance_useless
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:24:32.241763+00:00
-- url     : https://prove2.me/theorems/c351c27d-dd0b-4c2e-abb4-5a759a7fbabe
-- title:
--   Theorem 6.1 / (83): classical forward assistance is useless
-- statement:
--   Let $T$ be a memoryless CPTP channel between nonzero complex Hilbert spaces, and let $\Lambda\ge1$ be an integer classical alphabet size. Let $Q_{\rm cf}(T)$ allow an arbitrary finite number of forward messages at each block length, even superexponentially many. Encoding is a CP trace-nonincreasing instrument summing to a channel, each selected decoder is CPTP, and reliability uses the sum of unnormalized branch channel fidelities. Then
--   $$Q_{\rm cf}(T)=Q(T\otimes\mathrm{id}^c_\Lambda)=Q(T).$$
--   The fixed message budget $\Lambda^n$ gives the same capacity. No postselection, initial shared entanglement, or feedback is supplied. This is the uselessness of classical forward assistance.
-- source:
--   Tema Con Variazioni: Quantum Channel Capacity, arXiv:quant-ph/0311037v1, PDF p. 22, Theorem 6.1 / (83): classical forward assistance is useless

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

/-- PDF pp.22--24, Theorem 6.1, (83): arbitrary finite message budgets per
block, even superexponential, and every fixed positive classical alphabet. -/
theorem forwardAssistance_useless {I J : Type} [Nonempty I] [Nonempty J]
    (T : Operation I J) (hT : IsTraceClassChannel T) (messages : ℕ+) :
    instrumentForwardCapacity T (fun _ _ => True) =
      qubitReferenceCapacity (traceClassTensorMap T (classicalIdentity messages)) ∧
    qubitReferenceCapacity (traceClassTensorMap T (classicalIdentity messages)) = qubitReferenceCapacity T ∧
    instrumentForwardCapacity T (fun n k => (k : ℕ) = (messages : ℕ)^(n + 1)) = qubitReferenceCapacity T := by sorry

end QAlgorithms.Papers.Independent.Gap20.P07

end
