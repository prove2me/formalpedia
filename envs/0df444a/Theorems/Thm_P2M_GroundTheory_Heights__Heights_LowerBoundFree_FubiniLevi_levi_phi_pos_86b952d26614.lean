-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_levi_phi_pos_86b952d26614
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_levi_phi_pos_86b952d26614
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:28:29.989244+00:00
-- url     : https://prove2.me/theorems/bb34f03a-9fe7-427f-b0d4-e589f11789bb
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi levi phi pos 86b952d26614: P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi levi phi pos 86b952d26614
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi levi phi pos 86b952d26614 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi levi phi pos 86b952d26614 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/FubiniLevi.lean#L121-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/FubiniLevi.lean#L121-L151

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_FubiniLevi
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
variable {J : Type} [Fintype J]

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_levi_phi_pos_86b952d26614 {z w : (Σ _ : Unit, Fin 2) → ℂ} (hz : ∃ i, z ⟨(), i⟩ ≠ 0)
    (hw : ∀ c : ℂ, w ≠ fun p => c * z p) : 0 < leviForm phi z w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«FubiniLevi».«levi_phi_pos» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_levi_phi_pos_86b952d26614
