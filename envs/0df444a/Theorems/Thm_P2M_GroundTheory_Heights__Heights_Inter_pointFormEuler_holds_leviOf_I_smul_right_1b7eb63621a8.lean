-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_leviOf_I_smul_right_1b7eb63621a8
-- name    : P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_leviOf_I_smul_right_1b7eb63621a8
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:25:31.177222+00:00
-- url     : https://prove2.me/theorems/67b172d8-a5ee-4408-982f-f9044f7d0e6a
-- title:
--   P2 M Ground Theory Heights  Heights Inter point Form Euler holds levi Of I smul right 1b7eb63621a8: P2 M Ground Theory Heights  Heights Inter point Form Euler holds levi Of I smul right 1b7eb63621a8
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter point Form Euler holds levi Of I smul right 1b7eb63621a8 construction uses the P2 M Ground Theory Heights  Heights Inter point Form Euler holds levi Of I smul right 1b7eb63621a8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LeviOfRealSmulRight.lean#L34-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LeviOfRealSmulRight.lean#L34-L41

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

theorem P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_leviOf_I_smul_right_1b7eb63621a8 (H : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) (u v : Fin n → ℂ) :
    leviOf H u (Complex.I • v) = -Complex.I * leviOf H u v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«pointFormEuler_holds».«leviOf_I_smul_right» := P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_leviOf_I_smul_right_1b7eb63621a8
