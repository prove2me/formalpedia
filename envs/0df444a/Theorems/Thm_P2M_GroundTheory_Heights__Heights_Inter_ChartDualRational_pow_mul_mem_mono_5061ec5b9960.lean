-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartDualRational_pow_mul_mem_mono_5061ec5b9960
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ChartDualRational_pow_mul_mem_mono_5061ec5b9960
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:52.589466+00:00
-- url     : https://prove2.me/theorems/30c1b7e3-5728-4768-b6eb-78254d5f973c
-- title:
--   P2 M Ground Theory Heights  Heights Inter Chart Dual Rational pow mul mem mono 5061ec5b9960: P2 M Ground Theory Heights  Heights Inter Chart Dual Rational pow mul mem mono 5061ec5b9960
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Chart Dual Rational pow mul mem mono 5061ec5b9960 construction uses the P2 M Ground Theory Heights  Heights Inter Chart Dual Rational pow mul mem mono 5061ec5b9960 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartDualRational.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartDualRational.lean#L18-L21

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

theorem P2M_GroundTheory_Heights__Heights_Inter_ChartDualRational_pow_mul_mem_mono_5061ec5b9960 {u y : Ω} (hu : u ∈ R) {n m : ℕ} (hnm : n ≤ m) (h : u ^ n * y ∈ R) :
    u ^ m * y ∈ R := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ChartDualRational».«pow_mul_mem_mono» := P2M_GroundTheory_Heights__Heights_Inter_ChartDualRational_pow_mul_mem_mono_5061ec5b9960
