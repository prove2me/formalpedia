-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P07_capacity_noiselessFactor
-- name    : QAlgorithms.Papers.Independent.Gap20.P07.capacity_noiselessFactor
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:11:43.538971+00:00
-- url     : https://prove2.me/theorems/1e35eae4-56b4-4763-9104-3a716ce7502e
-- title:
--   Section 3.1: additivity with a noiseless factor
-- statement:
--   Let $T$ be a CPTP channel between arbitrary nonzero complex physical Hilbert spaces. Let $d\ge1$ and $s\ge2$ be integers giving a finite noiseless factor and a finite noiseless reference. Then
--   $$Q(T\otimes\mathrm{id}_d,\mathrm{id}_s)=Q(T,\mathrm{id}_s)+\frac{\log_2d}{\log_2s}.$$
--   The equality uses extended nonnegative capacities, allowing the physical channel $T$ to have infinite-dimensional systems or infinite capacity. It includes additivity for a pair of ideal channels.
-- source:
--   Tema Con Variazioni: Quantum Channel Capacity, arXiv:quant-ph/0311037v1, PDF p. 8, Section 3.1: additivity with a noiseless factor

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

/-- PDF p.8: exact additivity for a standard finite ideal reference and one
finite noiseless factor; the other channel's physical dimensions are unrestricted. -/
theorem capacity_noiselessFactor {I J : Type} [Nonempty I] [Nonempty J]
    (T : Operation I J) (hT : IsTraceClassChannel T)
    (d s : ℕ) (hd : 0 < d) (hs : 2 ≤ s) :
    relativeCapacity (traceClassTensorMap T (id : Operation (Fin d) (Fin d)))
      (id : Operation (Fin s) (Fin s)) =
      relativeCapacity T (id : Operation (Fin s) (Fin s)) +
        ENNReal.ofReal (Real.logb 2 d / Real.logb 2 s) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P07

end
