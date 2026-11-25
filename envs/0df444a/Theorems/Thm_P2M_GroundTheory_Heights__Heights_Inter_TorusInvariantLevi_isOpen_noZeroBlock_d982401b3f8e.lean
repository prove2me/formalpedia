-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_isOpen_noZeroBlock_d982401b3f8e
-- name    : P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_isOpen_noZeroBlock_d982401b3f8e
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:22:54.777517+00:00
-- url     : https://prove2.me/theorems/db8beb43-188b-4f2b-abf1-952b713c7af3
-- title:
--   P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi is Open no Zero Block d982401b3f8e: P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi is Open no Zero Block d982401b3f8e
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi is Open no Zero Block d982401b3f8e construction uses the P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi is Open no Zero Block d982401b3f8e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PTorusInvLevi.lean#L160-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PTorusInvLevi.lean#L160-L166

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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_isOpen_noZeroBlock_d982401b3f8e : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«TorusInvariantLevi».«isOpen_noZeroBlock» := P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_isOpen_noZeroBlock_d982401b3f8e
