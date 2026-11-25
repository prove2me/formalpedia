-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isAlgebraic_map_of_map_le_795ccb6161b2
-- name    : P2M_GroundTheory_Heights__Heights_Inter_isAlgebraic_map_of_map_le_795ccb6161b2
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:24:31.981926+00:00
-- url     : https://prove2.me/theorems/140729fb-f361-4405-81ce-c8cee9f1343f
-- title:
--   P2 M Ground Theory Heights  Heights Inter is Algebraic map of map le 795ccb6161b2: P2 M Ground Theory Heights  Heights Inter is Algebraic map of map le 795ccb6161b2
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter is Algebraic map of map le 795ccb6161b2 construction uses the P2 M Ground Theory Heights  Heights Inter is Algebraic map of map le 795ccb6161b2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PYYRatioBasis.lean#L12-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PYYRatioBasis.lean#L12-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StYYRatioBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StMobiusAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PYYRatioBasis
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.T
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Inter_isAlgebraic_map_of_map_le_795ccb6161b2 {Ω Φ : Type*} [Field Ω] [Field Φ] [Algebra ℚ Ω] [Algebra ℚ Φ]
    (f : Ω →ₐ[ℚ] Φ) {L : IntermediateField ℚ Ω} {M : IntermediateField ℚ Φ} (hLM : L.map f ≤ M) {y : Ω}
    (hy : IsAlgebraic L y) : IsAlgebraic M (f y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«isAlgebraic_map_of_map_le» := P2M_GroundTheory_Heights__Heights_Inter_isAlgebraic_map_of_map_le_795ccb6161b2
