-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartDualRational_mem_of_cover_10a84b863bcf
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ChartDualRational_mem_of_cover_10a84b863bcf
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:27:57.21958+00:00
-- url     : https://prove2.me/theorems/a2bcf3de-02fe-4c31-925f-bc665b85c826
-- title:
--   P2 M Ground Theory Heights  Heights Inter Chart Dual Rational mem of cover 10a84b863bcf: P2 M Ground Theory Heights  Heights Inter Chart Dual Rational mem of cover 10a84b863bcf
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Chart Dual Rational mem of cover 10a84b863bcf construction uses the P2 M Ground Theory Heights  Heights Inter Chart Dual Rational mem of cover 10a84b863bcf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartDualRational.lean#L23-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartDualRational.lean#L23-L39

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

theorem P2M_GroundTheory_Heights__Heights_Inter_ChartDualRational_mem_of_cover_10a84b863bcf {k : ℕ} {f c : Fin k → Ω} (hf : ∀ l, f l ∈ R) (hc : ∀ l, c l ∈ R) (hsum : ∑ l, c l * f l = 1)
    {y : Ω} (hy : ∀ l, ∃ N : ℕ, f l ^ N * y ∈ R) : y ∈ R := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ChartDualRational».«mem_of_cover» := P2M_GroundTheory_Heights__Heights_Inter_ChartDualRational_mem_of_cover_10a84b863bcf
