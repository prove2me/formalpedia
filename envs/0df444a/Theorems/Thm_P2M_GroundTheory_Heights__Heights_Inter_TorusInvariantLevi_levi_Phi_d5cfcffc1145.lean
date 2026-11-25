-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_levi_Phi_d5cfcffc1145
-- name    : P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_levi_Phi_d5cfcffc1145
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:23:01.740864+00:00
-- url     : https://prove2.me/theorems/6332c298-caf5-4b79-8f74-9ea7e6fbfdac
-- title:
--   P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi levi Phi d5cfcffc1145: P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi levi Phi d5cfcffc1145
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi levi Phi d5cfcffc1145 construction uses the P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi levi Phi d5cfcffc1145 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PTorusInvLevi.lean#L172-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PTorusInvLevi.lean#L172-L198

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

theorem P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_levi_Phi_d5cfcffc1145 {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (w : (Σ k, ι k) → ℂ) :
    leviForm (fun y => ∑ k, Real.log ((fsMetric (ι k)).ρ (fun i => y ⟨k, i⟩))) z w =
      ∑ k, leviForm phi (blk k z) (blk k w) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«TorusInvariantLevi».«levi_Phi» := P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_levi_Phi_d5cfcffc1145
