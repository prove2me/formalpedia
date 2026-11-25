-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_leviOf_sum_right_ebed156926f6
-- name    : P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_leviOf_sum_right_ebed156926f6
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:32:34.516531+00:00
-- url     : https://prove2.me/theorems/50c1521c-8302-55b1-873f-560bd15d065e
-- title:
--   P2 M Ground Theory Heights  Heights Inter point Form Euler holds levi Of sum right ebed156926f6: P2 M Ground Theory Heights  Heights Inter point Form Euler holds levi Of sum right ebed156926f6
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter point Form Euler holds levi Of sum right ebed156926f6 construction uses the P2 M Ground Theory Heights  Heights Inter point Form Euler holds levi Of sum right ebed156926f6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LeviOfRealSmulRight.lean#L43-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LeviOfRealSmulRight.lean#L43-L50

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

theorem P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_leviOf_sum_right_ebed156926f6 (H : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) (u : Fin n → ℂ) (v : Fin n → Fin n → ℂ) :
    leviOf H u (∑ j, v j) = ∑ j, leviOf H u (v j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«pointFormEuler_holds».«leviOf_sum_right» := P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_leviOf_sum_right_ebed156926f6
