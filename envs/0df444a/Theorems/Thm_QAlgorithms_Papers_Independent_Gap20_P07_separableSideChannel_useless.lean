-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P07_separableSideChannel_useless
-- name    : QAlgorithms.Papers.Independent.Gap20.P07.separableSideChannel_useless
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:25:13.994361+00:00
-- url     : https://prove2.me/theorems/376263dd-622c-4fca-8647-2c83be4a5fca
-- title:
--   Corollary 6.2 / (84): separable side channels are useless
-- statement:
--   Let $T$ and $R$ be CPTP channels between nonzero complex Hilbert spaces. Suppose $R$ factors operationally as measurement followed by preparation: a POVM with an arbitrary measurable outcome space has its actual probability law on every input state, and the output is the integrable barycenter of normalized prepared states. Then
--   $$Q(T\otimes R)=Q(T).$$
--   No finite or countable outcome restriction and no assumption of a product input is imposed. This is the separable-side-channel consequence of the forward-assistance theorem.
-- source:
--   Tema Con Variazioni: Quantum Channel Capacity, arXiv:quant-ph/0311037v1, PDF p. 23, Corollary 6.2 / (84): separable side channels are useless

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

/-- PDF p.23, Corollary 6.2, (84): operational measurement--preparation side
channels with arbitrary outcome spaces; no countable-decomposition assumption. -/
theorem separableSideChannel_useless {I J K L : Type}
    [Nonempty I] [Nonempty J] [Nonempty K] [Nonempty L]
    (T : Operation I J) (R : Operation K L) (hT : IsTraceClassChannel T)
    (hR : IsTraceClassChannel R) (hseparable : MeasurePrepare R) :
    qubitReferenceCapacity (traceClassTensorMap T R) = qubitReferenceCapacity T := by sorry

end QAlgorithms.Papers.Independent.Gap20.P07

end
