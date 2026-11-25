-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_add_2f0a77fa72a1
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_add_2f0a77fa72a1
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:13:51.891064+00:00
-- url     : https://prove2.me/theorems/97aa746d-9929-47a8-a64a-69bde59b68e5
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free is Value At add 2f0a77fa72a1: P2 M Ground Theory Heights  Heights Lower Bound Free is Value At add 2f0a77fa72a1
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free is Value At add 2f0a77fa72a1 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free is Value At add 2f0a77fa72a1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/Values.lean#L19-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/Values.lean#L19-L30

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
omit [Fintype K]

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_add_2f0a77fa72a1 {y : (Σ k, ι k) → Ω} {s t : Ω} {z : (Σ k, ι k) → ℂ} {v w : ℂ}
    (hv : IsValueAt y s z v) (hw : IsValueAt y t z w) : IsValueAt y (s + t) z (v + w) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«isValueAt_add» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_add_2f0a77fa72a1
