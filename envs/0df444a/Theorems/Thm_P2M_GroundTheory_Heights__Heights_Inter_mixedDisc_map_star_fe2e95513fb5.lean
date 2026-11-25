-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_mixedDisc_map_star_fe2e95513fb5
-- name    : P2M_GroundTheory_Heights__Heights_Inter_mixedDisc_map_star_fe2e95513fb5
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:34:54.109012+00:00
-- url     : https://prove2.me/theorems/8889ee54-c3ba-5818-933a-b892ad3b8643
-- title:
--   P2 M Ground Theory Heights  Heights Inter mixed Disc map star fe2e95513fb5: P2 M Ground Theory Heights  Heights Inter mixed Disc map star fe2e95513fb5
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter mixed Disc map star fe2e95513fb5 construction uses the P2 M Ground Theory Heights  Heights Inter mixed Disc map star fe2e95513fb5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFIntZeroMixed.lean#L78-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFIntZeroMixed.lean#L78-L88

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFIntZeroMixed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open Matrix Module ReciprocityTheory.ChartRestriction.G.Geo
variable {D : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Inter_mixedDisc_map_star_fe2e95513fb5 (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (fun k => (A k).map (starRingEnd ℂ)) = starRingEnd ℂ (mixedDisc A) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«mixedDisc_map_star» := P2M_GroundTheory_Heights__Heights_Inter_mixedDisc_map_star_fe2e95513fb5
