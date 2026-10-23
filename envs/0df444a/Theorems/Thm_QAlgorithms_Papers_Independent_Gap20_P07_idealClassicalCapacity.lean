-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P07_idealClassicalCapacity
-- name    : QAlgorithms.Papers.Independent.Gap20.P07.idealClassicalCapacity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T07:14:54.143984+00:00
-- url     : https://prove2.me/theorems/74479128-e780-4e71-9ffa-2b042d074db3
-- title:
--   Section 3.2: ideal quantum channel classical capacity
-- statement:
--   For every integer $d\ge1$, the unassisted classical capacity of an ideal $d$-level quantum channel is
--   $$C(\mathrm{id}_d)=\log_2d.$$
--   Here classical transmission uses the noiseless binary classical reference, equivalently complete dephasing followed by an ideal classical identity, with full-cb simulation error. CPTP coding has no shared entanglement or feedback. The equality includes achievability and the converse.
-- source:
--   Tema Con Variazioni: Quantum Channel Capacity, arXiv:quant-ph/0311037v1, PDF p. 10, Section 3.2: ideal quantum channel classical capacity

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

/-- PDF p.10: the ideal channel carries log2(d) classical bits per use,
with no shared entanglement or feedback; equality includes the converse. -/
theorem idealClassicalCapacity (d : ℕ) (hd : 0 < d) :
    relativeCapacity (id : Operation (Fin d) (Fin d)) (classicalIdentity 2) =
      ENNReal.ofReal (Real.logb 2 d) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P07

end
