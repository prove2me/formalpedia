-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartDualRational_exists_uniform_cde85cdc1d96
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ChartDualRational_exists_uniform_cde85cdc1d96
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:23:03.668417+00:00
-- url     : https://prove2.me/theorems/08f2c987-512b-4ff8-a926-17a24904df7e
-- title:
--   P2 M Ground Theory Heights  Heights Inter Chart Dual Rational exists uniform cde85cdc1d96: P2 M Ground Theory Heights  Heights Inter Chart Dual Rational exists uniform cde85cdc1d96
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Chart Dual Rational exists uniform cde85cdc1d96 construction uses the P2 M Ground Theory Heights  Heights Inter Chart Dual Rational exists uniform cde85cdc1d96 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartDualRational.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartDualRational.lean#L11-L14

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

theorem P2M_GroundTheory_Heights__Heights_Inter_ChartDualRational_exists_uniform_cde85cdc1d96 {α : Type*} [Fintype α] (P : α → ℕ → Prop) (mono : ∀ a n m, n ≤ m → P a n → P a m)
    (h : ∀ a, ∃ n, P a n) : ∃ n, ∀ a, P a n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ChartDualRational».«exists_uniform» := P2M_GroundTheory_Heights__Heights_Inter_ChartDualRational_exists_uniform_cde85cdc1d96
