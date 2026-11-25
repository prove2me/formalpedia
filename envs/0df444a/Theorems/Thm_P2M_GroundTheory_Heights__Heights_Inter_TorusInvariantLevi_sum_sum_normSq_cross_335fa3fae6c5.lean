-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_sum_sum_normSq_cross_335fa3fae6c5
-- name    : P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_sum_sum_normSq_cross_335fa3fae6c5
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:23:15.561808+00:00
-- url     : https://prove2.me/theorems/f2833f07-ae22-4a66-a276-53e3fad2e033
-- title:
--   P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi sum sum norm Sq cross 335fa3fae6c5: P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi sum sum norm Sq cross 335fa3fae6c5
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi sum sum norm Sq cross 335fa3fae6c5 construction uses the P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi sum sum norm Sq cross 335fa3fae6c5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PTorusInvLevi.lean#L22-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PTorusInvLevi.lean#L22-L52

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

theorem P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_sum_sum_normSq_cross_335fa3fae6c5 (z w : J → ℂ) :
    ∑ j, ∑ l, ‖z j * w l - z l * w j‖ ^ 2 =
      2 * (sqSum z * sqSum w - (reInner z w ^ 2 + reInner z (Complex.I • w) ^ 2)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«TorusInvariantLevi».«sum_sum_normSq_cross» := P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_sum_sum_normSq_cross_335fa3fae6c5
