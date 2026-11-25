-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_pow_d9d354672a82
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_pow_d9d354672a82
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:14:33.951472+00:00
-- url     : https://prove2.me/theorems/029f7a0b-4c0f-4afb-94b0-83ce00620b24
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free is Value At pow d9d354672a82: P2 M Ground Theory Heights  Heights Lower Bound Free is Value At pow d9d354672a82
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free is Value At pow d9d354672a82 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free is Value At pow d9d354672a82 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/Values.lean#L46-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/Values.lean#L46-L50

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

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_pow_d9d354672a82 {y : (Σ k, ι k) → Ω} {s : Ω} {z : (Σ k, ι k) → ℂ} {v : ℂ}
    (hv : IsValueAt y s z v) (n : ℕ) : IsValueAt y (s ^ n) z (v ^ n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«isValueAt_pow» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_pow_d9d354672a82
