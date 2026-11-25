-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_row_le_91853da86e09
-- name    : P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_row_le_91853da86e09
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:23:11.151614+00:00
-- url     : https://prove2.me/theorems/8841353b-ff31-4ed3-9d4d-526fe3e20c1d
-- title:
--   P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi row le 91853da86e09: P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi row le 91853da86e09
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi row le 91853da86e09 construction uses the P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi row le 91853da86e09 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PTorusInvLevi.lean#L54-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PTorusInvLevi.lean#L54-L57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StTorusInvLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_FubiniLevi
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PTorusInvLevi
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
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
open GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi
set_option linter.unusedSectionVars false
variable {J : Type} [Fintype J]

theorem P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_row_le_91853da86e09 (z w : J → ℂ) (q : J) :
    ∑ l, ‖z q * w l - z l * w q‖ ^ 2 ≤ ∑ j, ∑ l, ‖z j * w l - z l * w j‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«TorusInvariantLevi».«row_le» := P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_row_le_91853da86e09
