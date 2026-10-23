-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P07_capacity_bottleneck
-- name    : QAlgorithms.Papers.Independent.Gap20.P07.capacity_bottleneck
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:10:24.239382+00:00
-- url     : https://prove2.me/theorems/db519797-3774-48eb-b92c-2eb1dc21ff29
-- title:
--   Section 3.1 / (15): bottleneck inequality
-- statement:
--   Let $T_2:H_1\to H_2$ and $T_1:H_2\to H_3$ be composable CPTP channels, and let $S$ be any CPTP reference channel, all on nonzero complex Hilbert spaces. For the full-cb relative capacities of Definition 2.1,
--   $$Q(T_1\circ T_2,S)\le\min\{Q(T_1,S),Q(T_2,S)\}.$$
--   The reference may be noisy. This is the capacity bottleneck property for sequential channel use.
-- source:
--   Tema Con Variazioni: Quantum Channel Capacity, arXiv:quant-ph/0311037v1, PDF p. 8, Section 3.1 / (15): bottleneck inequality

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

/-- PDF p.8, (15): bottleneck inequality, including arbitrary noisy references. -/
theorem capacity_bottleneck {I J K A B : Type}
    [Nonempty I] [Nonempty J] [Nonempty K] [Nonempty A] [Nonempty B]
    (T1 : Operation J K) (T2 : Operation I J) (S : Operation A B)
    (h1 : IsTraceClassChannel T1) (h2 : IsTraceClassChannel T2) (hS : IsTraceClassChannel S) :
    relativeCapacity (T1 ∘ T2) S ≤ min (relativeCapacity T1 S) (relativeCapacity T2 S) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P07

end
