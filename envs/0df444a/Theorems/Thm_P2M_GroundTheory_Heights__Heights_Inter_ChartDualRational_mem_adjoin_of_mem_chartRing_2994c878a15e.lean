-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartDualRational_mem_adjoin_of_mem_chartRing_2994c878a15e
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ChartDualRational_mem_adjoin_of_mem_chartRing_2994c878a15e
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:46:09.922002+00:00
-- url     : https://prove2.me/theorems/ae44c335-fc12-5caf-b271-2b04ffc87bb5
-- title:
--   P2 M Ground Theory Heights  Heights Inter Chart Dual Rational mem adjoin of mem chart Ring 2994c878a15e: P2 M Ground Theory Heights  Heights Inter Chart Dual Rational mem adjoin of mem chart Ring 2994
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Chart Dual Rational mem adjoin of mem chart Ring 2994c878a15e construction uses the P2 M Ground Theory Heights  Heights Inter Chart Dual Rational mem adjoin of mem chart Ring 2994c878a15e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartDualRational.lean#L41-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartDualRational.lean#L41-L47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartDualRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartDualRational
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
open GroundTheory.Heights₂.Heights.Inter.ChartDualRational
variable {Ω : Type*} [Field Ω] {R : Subalgebra ℤ Ω}

theorem P2M_GroundTheory_Heights__Heights_Inter_ChartDualRational_mem_adjoin_of_mem_chartRing_2994c878a15e [CharZero Ω] {ι : Type*} (x : ι → Ω) (i : ι) {a : Ω} (ha : a ∈ chartRing ℤ x i) :
    a ∈ IntermediateField.adjoin ℚ (Set.range fun j ↦ x j / x i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ChartDualRational».«mem_adjoin_of_mem_chartRing» := P2M_GroundTheory_Heights__Heights_Inter_ChartDualRational_mem_adjoin_of_mem_chartRing_2994c878a15e
