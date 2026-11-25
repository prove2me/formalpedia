-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_lagrange_9c3712389ff7
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_lagrange_9c3712389ff7
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:31:30.05086+00:00
-- url     : https://prove2.me/theorems/1c5a7f82-55d7-4a39-8a99-16dd8d3771bb
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi lagrange 9c3712389ff7: P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi lagrange 9c3712389ff7
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi lagrange 9c3712389ff7 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi lagrange 9c3712389ff7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/FubiniLevi.lean#L113-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/FubiniLevi.lean#L113-L119

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

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_lagrange_9c3712389ff7 (z w : (Σ _ : Unit, Fin 2) → ℂ) :
    sqSum z * sqSum w - (reInner z w ^ 2 + reInner z (Complex.I • w) ^ 2) =
      Complex.normSq (z ⟨(), 0⟩ * w ⟨(), 1⟩ - z ⟨(), 1⟩ * w ⟨(), 0⟩) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«FubiniLevi».«lagrange» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_lagrange_9c3712389ff7
