-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_norm_mul_self_le_sum_96ee2cbc5748
-- name    : P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_norm_mul_self_le_sum_96ee2cbc5748
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:22:53.881781+00:00
-- url     : https://prove2.me/theorems/a24d90de-83b8-4452-956a-828dde895d2b
-- title:
--   P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi norm mul self le sum 96ee2cbc5748: P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi norm mul self le sum 96ee2cbc5748
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi norm mul self le sum 96ee2cbc5748 construction uses the P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi norm mul self le sum 96ee2cbc5748 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PTorusInvLevi.lean#L121-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PTorusInvLevi.lean#L121-L129

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

theorem P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_norm_mul_self_le_sum_96ee2cbc5748 (v : J → ℂ) : ‖v‖ * ‖v‖ ≤ ∑ p, ‖v p‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«TorusInvariantLevi».«norm_mul_self_le_sum» := P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_norm_mul_self_le_sum_96ee2cbc5748
