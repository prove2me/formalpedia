-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_leviOf_add_right_4973c981d991
-- name    : P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_leviOf_add_right_4973c981d991
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:58.4008+00:00
-- url     : https://prove2.me/theorems/5b81b7c5-ae02-4acb-9f1f-7297ba894f01
-- title:
--   P2 M Ground Theory Heights  Heights Inter point Form Euler holds levi Of add right 4973c981d991: P2 M Ground Theory Heights  Heights Inter point Form Euler holds levi Of add right 4973c981d991
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter point Form Euler holds levi Of add right 4973c981d991 construction uses the P2 M Ground Theory Heights  Heights Inter point Form Euler holds levi Of add right 4973c981d991 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LeviOfRealSmulRight.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LeviOfRealSmulRight.lean#L22-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExMap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LeviOfRealSmulRight
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
open Matrix Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.Inter.pointFormEuler_holds
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_leviOf_add_right_4973c981d991 (H : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) (u v w : Fin n → ℂ) :
    leviOf H u (v + w) = leviOf H u v + leviOf H u w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«pointFormEuler_holds».«leviOf_add_right» := P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_leviOf_add_right_4973c981d991
