-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_inv_367f1c26964d
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_inv_367f1c26964d
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:14:01.452267+00:00
-- url     : https://prove2.me/theorems/33a03983-7b61-4a21-a76a-5da928c4e6d1
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free is Value At inv 367f1c26964d: P2 M Ground Theory Heights  Heights Lower Bound Free is Value At inv 367f1c26964d
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free is Value At inv 367f1c26964d construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free is Value At inv 367f1c26964d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/Values.lean#L36-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/Values.lean#L36-L44

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

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_inv_367f1c26964d {y : (Σ k, ι k) → Ω} {s : Ω} {z : (Σ k, ι k) → ℂ} {v : ℂ}
    (hv : IsValueAt y s z v) (hs : s ≠ 0) (hv0 : v ≠ 0) : IsValueAt y s⁻¹ z v⁻¹ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«isValueAt_inv» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_inv_367f1c26964d
