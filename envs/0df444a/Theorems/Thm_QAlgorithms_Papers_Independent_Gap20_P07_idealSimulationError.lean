-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P07_idealSimulationError
-- name    : QAlgorithms.Papers.Independent.Gap20.P07.idealSimulationError
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T07:14:12.009495+00:00
-- url     : https://prove2.me/theorems/7ab6ff27-f150-4635-a624-ff9cd670d5bd
-- title:
--   Section 3.2 / (20),(21): exact embedding and dimensional obstruction
-- statement:
--   Let $n,m\ge1$ be integers and let $\Delta(\mathrm{id}_n,\mathrm{id}_m)$ be the infimum of the full-cb error over all CPTP encoders and decoders simulating an ideal $m$-level system through an ideal $n$-level system. Then
--   $$m\le n\ \Longrightarrow\ \Delta=0,\qquad m\ge n\ \Longrightarrow\ \Delta\ge1-\frac nm.$$
--   The first branch pads the logical $m\times m$ matrix into $n\times n$ matrices; the second is the dimensional obstruction. These estimates include equal dimensions.
-- source:
--   Tema Con Variazioni: Quantum Channel Capacity, arXiv:quant-ph/0311037v1, PDF p. 9, Section 3.2 / (20),(21): exact embedding and dimensional obstruction

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

/-- PDF pp.9--10, (20)--(21): exact embedding and dimensional obstruction.
The surrounding prose reverses the padding dimensions; the formulas fix them. -/
theorem idealSimulationError (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    (m ≤ n → codingSimulationDistance (id : Operation (Fin n) (Fin n))
      (id : Operation (Fin m) (Fin m)) = 0) ∧
    (n ≤ m → ENNReal.ofReal (1 - (n : ℝ) / m) ≤
      codingSimulationDistance (id : Operation (Fin n) (Fin n)) (id : Operation (Fin m) (Fin m))) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P07

end
