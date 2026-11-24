-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_exists_bounded_frame_c1f354ee7137
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_exists_bounded_frame_c1f354ee7137
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:28:30.930793+00:00
-- url     : https://prove2.me/theorems/14cfdc47-4d7d-4532-80ec-763fb9ddffee
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Forms exists bounded frame c1f354ee7137: P2 M Ground Theory Heights  Heights Inter Diagonal Forms exists bounded frame c1f354ee7137
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Forms exists bounded frame c1f354ee7137 construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Forms exists bounded frame c1f354ee7137 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagForms.lean#L76-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagForms.lean#L76-L129

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagForms
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.DiagonalForms
variable {Ω : Type*} [Field Ω] {ι : Type*} {E : Type*} [AddCommGroup E] [Module Ω E] {x : ι → Ω}

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_exists_bounded_frame_c1f354ee7137 (B : ChartBundle ℤ x 2 E) (i : ι) (hi : x i ≠ 0) :
    ∃ (f : Ω) (b : Module.Basis (Fin 2) Ω E) (N : ℕ), f ∈ chartRing ℤ x i ∧ f ≠ 0 ∧
      (∀ q, ∃ n : ℕ, f ^ n • b q ∈ B.lat i) ∧
      ∀ v ∈ B.lat i, ∀ q, f ^ N * b.repr v q ∈ chartRing ℤ x i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalForms».«exists_bounded_frame» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_exists_bounded_frame_c1f354ee7137
