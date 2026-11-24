-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RatioField_map_mem_8496003472e3
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RatioField_map_mem_8496003472e3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:29.46018+00:00
-- url     : https://prove2.me/theorems/b18fb3a3-7873-497b-846c-ce59a52c13b6
-- title:
--   P2 M Ground Theory Heights  Heights Inter Ratio Field map mem 8496003472e3: P2 M Ground Theory Heights  Heights Inter Ratio Field map mem 8496003472e3
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Ratio Field map mem 8496003472e3 construction uses the P2 M Ground Theory Heights  Heights Inter Ratio Field map mem 8496003472e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsAlgebraicMapAdjoin.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsAlgebraicMapAdjoin.lean#L13-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StWWRatioBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsAlgebraicMapAdjoin
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
open ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
variable {Ω Φ : Type*} [Field Ω] [Field Φ] [Algebra Ω Φ]

theorem P2M_GroundTheory_Heights__Heights_Inter_RatioField_map_mem_8496003472e3 [CharZero Ω] [CharZero Φ] {S : Set Ω} {L : IntermediateField ℚ Φ}
    (hS : ∀ w ∈ S, algebraMap Ω Φ w ∈ L) {z : Ω} (hz : z ∈ IntermediateField.adjoin ℚ S) :
    algebraMap Ω Φ z ∈ L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RatioField».«map_mem» := P2M_GroundTheory_Heights__Heights_Inter_RatioField_map_mem_8496003472e3
