-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P07_capacity_superadditive
-- name    : QAlgorithms.Papers.Independent.Gap20.P07.capacity_superadditive
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:11:01.843997+00:00
-- url     : https://prove2.me/theorems/84babdc2-8662-4612-8e32-c3d3a0aa0661
-- title:
--   Section 3.1 / (16): tensor superadditivity
-- statement:
--   Let $T_1,T_2$ be CPTP channels on nonzero complex Hilbert spaces and let $S$ be any CPTP reference channel. Then their extended nonnegative relative capacities satisfy
--   $$Q(T_1\otimes T_2,S)\ge Q(T_1,S)+Q(T_2,S).$$
--   This gives superadditivity for parallel use; it does not assert additivity for arbitrary noisy factors.
-- source:
--   Tema Con Variazioni: Quantum Channel Capacity, arXiv:quant-ph/0311037v1, PDF p. 8, Section 3.1 / (16): tensor superadditivity

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

/-- PDF p.8, (16): tensor superadditivity, with no general additivity assumption. -/
theorem capacity_superadditive {I J K L A B : Type}
    [Nonempty I] [Nonempty J] [Nonempty K] [Nonempty L] [Nonempty A] [Nonempty B]
    (T1 : Operation I J) (T2 : Operation K L) (S : Operation A B)
    (h1 : IsTraceClassChannel T1) (h2 : IsTraceClassChannel T2) (hS : IsTraceClassChannel S) :
    relativeCapacity T1 S + relativeCapacity T2 S ≤
      relativeCapacity (traceClassTensorMap T1 T2) S := by sorry

end QAlgorithms.Papers.Independent.Gap20.P07

end
