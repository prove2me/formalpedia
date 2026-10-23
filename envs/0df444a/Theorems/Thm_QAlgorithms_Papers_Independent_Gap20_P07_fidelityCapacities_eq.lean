-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P07_fidelityCapacities_eq
-- name    : QAlgorithms.Papers.Independent.Gap20.P07.fidelityCapacities_eq
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:03:47.385127+00:00
-- url     : https://prove2.me/theorems/174aeb73-56a6-4973-8ce6-d8cea5a63dc8
-- title:
--   Sections 2.3–2.5 and 4.2–4.4: fidelity capacity equivalences
-- statement:
--   Let $T$ be a memoryless CPTP channel between nonzero complex Hilbert spaces. For each positive block length choose one CPTP code on a finite, nonzero logical space of dimension $d_n$, and use $\limsup_n\log_2(d_n)/n$ as its rate. Define capacities by requiring, respectively, minimum normalized pure-state survival fidelity, the infimum of entanglement fidelity over density states, normalized Haar average fidelity, or entanglement fidelity of the maximally mixed state, to tend to one. All overlaps are squared. Then
--   $$Q_{\min}(T)=Q_{e,\min}(T)=Q_{\rm av}(T)=Q_c(T)=Q(T).$$
--   Each capacity is the extended nonnegative supremum of positive rates. The mean criteria require selecting suitable logical subspaces; no dimension-independent norm bound for the original channel is asserted.
-- source:
--   Tema Con Variazioni: Quantum Channel Capacity, arXiv:quant-ph/0311037v1, PDF p. 4, Sections 2.3–2.5 and 4.2–4.4: fidelity capacity equivalences

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

/-- PDF pp.4--5,13--18: all four fidelity capacity definitions coincide.
Average/channel fidelity require expurgation, not an original-channel norm bound. -/
theorem fidelityCapacities_eq {I J : Type} [Nonempty I] [Nonempty J]
    (T : Operation I J) (hT : IsTraceClassChannel T) :
    ∀ c : FidelityCriterion, fidelityCapacity T c = qubitReferenceCapacity T := by sorry

end QAlgorithms.Papers.Independent.Gap20.P07

end
