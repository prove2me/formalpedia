-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P07_referenceUnits
-- name    : QAlgorithms.Papers.Independent.Gap20.P07.referenceUnits
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:01:26.933163+00:00
-- url     : https://prove2.me/theorems/40c1d287-4aaf-41c2-b0c5-c8a54201fc30
-- title:
--   Section 2.1 / (3),(19): change of reference units
-- statement:
--   Let $T$ be any CPTP channel between nonzero complex Hilbert spaces, and let $m,n\ge2$ be integer reference dimensions. Write $Q(T,\mathrm{id}_d)$ for Definition 2.1 capacity relative to an ideal $d$-level channel. Then
--   $$Q(T,\mathrm{id}_n)=\frac{\log_2m}{\log_2n}\,Q(T,\mathrm{id}_m).$$
--   The scalar product is taken in the extended nonnegative reals. Changing the nontrivial reference dimension changes only the unit of capacity; dimension one is excluded from the logarithmic ratio.
-- source:
--   Tema Con Variazioni: Quantum Channel Capacity, arXiv:quant-ph/0311037v1, PDF p. 3, Section 2.1 / (3),(19): change of reference units

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

/-- PDF pp.3,9, (3),(19): only nontrivial reference systems have a log ratio. -/
theorem referenceUnits {I J : Type} [Nonempty I] [Nonempty J]
    (T : Operation I J) (hT : IsTraceClassChannel T)
    (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) :
    relativeCapacity T (id : Operation (Fin n) (Fin n)) =
      ENNReal.ofReal (Real.logb 2 m / Real.logb 2 n) *
        relativeCapacity T (id : Operation (Fin m) (Fin m)) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P07

end
