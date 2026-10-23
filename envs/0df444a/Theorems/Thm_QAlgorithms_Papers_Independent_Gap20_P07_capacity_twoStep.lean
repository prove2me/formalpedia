-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P07_capacity_twoStep
-- name    : QAlgorithms.Papers.Independent.Gap20.P07.capacity_twoStep
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:12:34.387966+00:00
-- url     : https://prove2.me/theorems/c67b3580-6996-491e-8296-21b99cca6c14
-- title:
--   Section 3.1 / (17): two-step coding inequality
-- statement:
--   Let $T_1,T_2,T_3$ be arbitrary CPTP channels on nonzero complex Hilbert spaces, with relative capacities defined by memoryless powers, CPTP coding, and full-cb error. Then
--   $$Q(T_1,T_3)\ge Q(T_1,T_2)Q(T_2,T_3).$$
--   Multiplication is in the extended nonnegative reals, with $0\cdot\infty=0$. Introducing an intermediate channel cannot improve the direct simulation rate.
-- source:
--   Tema Con Variazioni: Quantum Channel Capacity, arXiv:quant-ph/0311037v1, PDF p. 8, Section 3.1 / (17): two-step coding inequality

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

/-- PDF p.8, (17): two-step coding, with extended nonnegative multiplication. -/
theorem capacity_twoStep {I J K L A B : Type}
    [Nonempty I] [Nonempty J] [Nonempty K] [Nonempty L] [Nonempty A] [Nonempty B]
    (T1 : Operation I J) (T2 : Operation K L) (T3 : Operation A B)
    (h1 : IsTraceClassChannel T1) (h2 : IsTraceClassChannel T2) (h3 : IsTraceClassChannel T3) :
    relativeCapacity T1 T2 * relativeCapacity T2 T3 ≤ relativeCapacity T1 T3 := by sorry

end QAlgorithms.Papers.Independent.Gap20.P07

end
