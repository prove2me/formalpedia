-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P07_generationCapacity_eq
-- name    : QAlgorithms.Papers.Independent.Gap20.P07.generationCapacity_eq
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:23:12.857585+00:00
-- url     : https://prove2.me/theorems/270e9721-81b6-4bc1-afa6-891ccda05c47
-- title:
--   Sections 2.5 and 4.5: entanglement-generation capacity equals Q
-- statement:
--   Let $T$ be a memoryless CPTP channel between nonzero complex Hilbert spaces. For each positive block length, permit a finite nonzero logical space and any normalized pure reference/input state $\Gamma_n$. Require the squared overlap of $(\mathrm{id}\otimes D_nT^{\otimes n}E_n)(|\Gamma_n\rangle\langle\Gamma_n|)$ with the maximally entangled target to tend to one. Let $Q_{\rm gen}(T)$ be the extended supremum of positive limsup logical-dimension rates. Then
--   $$Q_{\rm gen}(T)=Q(T).$$
--   The input $\Gamma_n$ need not be maximally entangled and there is no initially shared entanglement between sender and receiver. This identifies the entanglement-generation variant.
-- source:
--   Tema Con Variazioni: Quantum Channel Capacity, arXiv:quant-ph/0311037v1, PDF p. 5, Sections 2.5 and 4.5: entanglement-generation capacity equals Q

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

/-- PDF pp.5,19--20: arbitrary normalized entanglement-generation inputs are
allowed; teleportation and removal of forward communication yield Q. -/
theorem generationCapacity_eq {I J : Type} [Nonempty I] [Nonempty J]
    (T : Operation I J) (hT : IsTraceClassChannel T) :
    variableSourceGenerationCapacity T = qubitReferenceCapacity T := by sorry

end QAlgorithms.Papers.Independent.Gap20.P07

end
