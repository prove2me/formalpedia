-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_measure_eq_zero_of_finite_inter_lines__6259a2ae9d61
-- name    : P2M_GlobalTheory_T_measure_eq_zero_of_finite_inter_lines__6259a2ae9d61
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:10:01.317857+00:00
-- url     : https://prove2.me/theorems/7c64553c-8c43-453a-ad5f-94b3962fd9a5
-- title:
--   P2 M Global Theory T measure eq zero of finite inter lines  6259a2ae9d61: P2 M Global Theory T measure eq zero of finite inter lines  6259a2ae9d61
-- statement:
--   The P2 M Global Theory T measure eq zero of finite inter lines  6259a2ae9d61 construction uses the P2 M Global Theory T measure eq zero of finite inter lines  6259a2ae9d61 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MeasureEqZeroOfFiniteInterLinesStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MeasureEqZeroOfFiniteInterLinesStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MeasureEqZeroOfFiniteInterLines
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MeasureEqZeroOfFiniteInterLinesStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_measure_eq_zero_of_finite_inter_lines__6259a2ae9d61 : ∀ (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (Z : Set V), MeasurableSet Z → ∀ y : V, (∀ x : V, {t : K | x + t • y ∈ Z}.Finite) → μ Z = 0 := by sorry

alias «GlobalTheory».«T».«measure_eq_zero_of_finite_inter_lines'» := P2M_GlobalTheory_T_measure_eq_zero_of_finite_inter_lines__6259a2ae9d61
