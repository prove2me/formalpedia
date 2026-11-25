-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_exists_isValueAt_of_mem_chartRing_2e95e89691d2
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_exists_isValueAt_of_mem_chartRing_2e95e89691d2
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:14:39.690724+00:00
-- url     : https://prove2.me/theorems/a2d4c8b2-8ecb-4938-a204-cdaab2cd48ee
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free exists is Value At of mem chart Ring 2e95e89691d2: P2 M Ground Theory Heights  Heights Lower Bound Free exists is Value At of mem chart Ring 2e95e8
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free exists is Value At of mem chart Ring 2e95e89691d2 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free exists is Value At of mem chart Ring 2e95e89691d2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/Values.lean#L95-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/Values.lean#L95-L120

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_IsFrameOverLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Values
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {Ω : Type} [Field Ω]

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_exists_isValueAt_of_mem_chartRing_2e95e89691d2 {y : (Σ k, ι k) → Ω} {c : (k : K) → ι k}
    {z : (Σ k, ι k) → ℂ} (hyc : segreCoord y c ≠ 0) (hz : ∀ k, z ⟨k, c k⟩ ≠ 0) {r : Ω}
    (hr : r ∈ chartRing ℤ (segreCoord y) c) : ∃ v, IsValueAt y r z v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«exists_isValueAt_of_mem_chartRing» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_exists_isValueAt_of_mem_chartRing_2e95e89691d2
