-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P49_zeroCapacityComposition
-- name    : QAlgorithms.Papers.Independent.Claimed50.P49.zeroCapacityComposition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:13:43.696839+00:00
-- url     : https://prove2.me/theorems/46757a47-1393-4605-805b-b538c7e3dc57
-- title:
--   Zero capacity under composition
-- statement:
--   Here $Q$ denotes unrestricted, unassisted memoryless quantum capacity, defined by arbitrary trace-class CPTP encoders and decoders and entanglement-transmission fidelity tending to one; no energy constraint or Gaussian coding restriction is imposed. Let $E_1,E_2$ be arbitrary trace-class CPTP endomorphisms on the same nonzero complete Hilbert space. If $Q(E_1)=0$, then
--
--   $$Q(E_1\circ E_2)=Q(E_2\circ E_1)=0.$$
--
--   This is composition data processing for quantum capacity; it concerns pre- and postprocessing by channels.
-- source:
--   One-mode Bosonic Gaussian channels: a full weak-degradability classification, arXiv:quant-ph/0609013v2, PDF p. 17, §4, preliminary fact

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P49

noncomputable section

open scoped BigOperators ENNReal Topology

open Filter MeasureTheory

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P14

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

namespace QAlgorithms.Papers.Independent.Claimed50.P49

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Section 4, PDF pp.17-18: zero capacity survives pre- and postcomposition.
Capacity is unrestricted unassisted memoryless trace-class capacity, not Gaussian
coding capacity; this makes no assertion about tensor-product superactivation. -/
theorem zeroCapacityComposition {I : Type} [Nonempty I]
    (E1 E2 : Operation I I) (h1 : IsTraceClassChannel E1) (h2 : IsTraceClassChannel E2)
    (hzero : operationalTraceClassCapacity E1 = 0) :
    operationalTraceClassCapacity (E1 ∘ E2) = 0 ∧
    operationalTraceClassCapacity (E2 ∘ E1) = 0 := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P49

end
