-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_chart_bound_14af4c518f29
-- name    : P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_chart_bound_14af4c518f29
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:22:49.612809+00:00
-- url     : https://prove2.me/theorems/0737d24f-7582-4182-a1dc-1bb11cdb0e16
-- title:
--   P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi chart bound 14af4c518f29: P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi chart bound 14af4c518f29
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi chart bound 14af4c518f29 construction uses the P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi chart bound 14af4c518f29 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PTorusInvLevi.lean#L72-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PTorusInvLevi.lean#L72-L95

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

theorem P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_chart_bound_14af4c518f29 {z w : J → ℂ} {q : J} (hq : ∀ j, ‖z j‖ ≤ ‖z q‖) (hz : z q ≠ 0) :
    ∑ l, ‖(z q * w l - z l * w q) / z q ^ 2‖ ^ 2 ≤ 4 * (Fintype.card J : ℝ) ^ 2 * leviForm phi z w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«TorusInvariantLevi».«chart_bound» := P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_chart_bound_14af4c518f29
