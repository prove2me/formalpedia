-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P07_qaepEntropyCapacity_eq
-- name    : QAlgorithms.Papers.Independent.Gap20.P07.qaepEntropyCapacity_eq
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:04:32.211508+00:00
-- url     : https://prove2.me/theorems/a1bf98b7-3ed1-46fc-a140-ec95070dff93
-- title:
--   Sections 2.6 and 4.4: entropy capacity for QAEP sources
-- statement:
--   Let $T$ be a memoryless CPTP channel on nonzero physical Hilbert spaces. A source consists of finite nonzero block spaces and density states $\rho_n$; its entropy rate is $\limsup_n S(\rho_n)/n$, with entropy in bits. It satisfies QAEP at finite rate $R\ge0$ if this entropy rate is $R$ and, for every $\eta>0$, the total spectral mass in
--   $$2^{-n(R+\eta)}\le\lambda\le2^{-n(R-\eta)}$$
--   tends to one. Let $Q_{\rm QAEP}(T)$ be the extended supremum of entropy rates of QAEP sources transmitted by CPTP codes with squared entanglement fidelity tending to one. Then
--   $$Q_{\rm QAEP}(T)=Q(T).$$
--   Typical restrictions are normalized only at positive retained mass. QAEP does not impose a bound on every eigenvalue of the original source state. This version covers the source class specified by the paper without restricting it to product sources.
-- source:
--   Tema Con Variazioni: Quantum Channel Capacity, arXiv:quant-ph/0311037v1, PDF p. 5, Sections 2.6 and 4.4: entropy capacity for QAEP sources

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

/-- PDF pp.5--6,18--19: QAEP source capacity equals Q. The definition uses
concentrated typical mass; it does not impose the erroneous global eigenvalue bound. -/
theorem qaepEntropyCapacity_eq {I J : Type} [Nonempty I] [Nonempty J]
    (T : Operation I J) (hT : IsTraceClassChannel T) :
    sourceEntropyCapacity T QuantumSource.QAEP = qubitReferenceCapacity T := by sorry

end QAlgorithms.Papers.Independent.Gap20.P07

end
