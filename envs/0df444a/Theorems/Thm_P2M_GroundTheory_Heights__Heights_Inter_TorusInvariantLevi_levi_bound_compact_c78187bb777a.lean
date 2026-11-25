-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_levi_bound_compact_c78187bb777a
-- name    : P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_levi_bound_compact_c78187bb777a
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:23:30.916325+00:00
-- url     : https://prove2.me/theorems/47df2e9b-3f85-4db0-bad0-d609c4d9edea
-- title:
--   P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi levi bound compact c78187bb777a: P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi levi bound compact c78187bb777a
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi levi bound compact c78187bb777a construction uses the P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi levi bound compact c78187bb777a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PTorusInvLevi.lean#L97-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PTorusInvLevi.lean#L97-L119

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

theorem P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_levi_bound_compact_c78187bb777a {φ : (J → ℂ) → ℝ} {U Q : Set (J → ℂ)} (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ U)
    (hQ : IsCompact Q) (hQU : Q ⊆ U) :
    ∃ M, 0 ≤ M ∧ ∀ x ∈ Q, ∀ v, |ReciprocityTheory.AnForm.levi φ x v| ≤ M * (‖v‖ * ‖v‖) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«TorusInvariantLevi».«levi_bound_compact» := P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_levi_bound_compact_c78187bb777a
