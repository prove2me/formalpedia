-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P07_idealCapacity
-- name    : QAlgorithms.Papers.Independent.Gap20.P07.idealCapacity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T07:13:31.56279+00:00
-- url     : https://prove2.me/theorems/5cd650d6-e6ca-4961-93e0-4c0adfda77d4
-- title:
--   Section 3.2 / (18): ideal channel capacity
-- statement:
--   Let $n\ge1$ and $m\ge2$ be integers. The capacity of an ideal $n$-level channel relative to an ideal $m$-level channel is
--   $$Q(\mathrm{id}_n,\mathrm{id}_m)=\frac{\log_2n}{\log_2m}.$$
--   The one-dimensional physical channel gives zero; the one-dimensional reference is excluded from the quotient. This calibrates ideal quantum transmission in bits.
-- source:
--   Tema Con Variazioni: Quantum Channel Capacity, arXiv:quant-ph/0311037v1, PDF p. 9, Section 3.2 / (18): ideal channel capacity

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

/-- PDF pp.9--10, (18): n=1 gives zero; the reference dimension exceeds one. -/
theorem idealCapacity (n m : ℕ) (hn : 0 < n) (hm : 2 ≤ m) :
    relativeCapacity (id : Operation (Fin n) (Fin n)) (id : Operation (Fin m) (Fin m)) =
      ENNReal.ofReal (Real.logb 2 n / Real.logb 2 m) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P07

end
