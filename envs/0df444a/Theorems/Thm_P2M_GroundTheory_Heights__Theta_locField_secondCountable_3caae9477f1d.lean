-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_locField_secondCountable_3caae9477f1d
-- name    : P2M_GroundTheory_Heights__Theta_locField_secondCountable_3caae9477f1d
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:42:40.656096+00:00
-- url     : https://prove2.me/theorems/7b97c18d-04eb-43b7-bce2-24c7332c127b
-- title:
--   P2 M Ground Theory Heights  Theta loc Field second Countable 3caae9477f1d: P2 M Ground Theory Heights  Theta loc Field second Countable 3caae9477f1d
-- statement:
--   The P2 M Ground Theory Heights  Theta loc Field second Countable 3caae9477f1d construction uses the P2 M Ground Theory Heights  Theta loc Field second Countable 3caae9477f1d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/LocallyCompactField/Countability.lean#L192-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/LocallyCompactField/Countability.lean#L192-L200

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LocallyCompactField_Countability
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open MeasureTheory Measure Filter Topology Set
open scoped NNReal ENNReal Pointwise
variable {R : Type*} [Field R] [TopologicalSpace R] [IsTopologicalRing R]
variable [LocallyCompactSpace R] [T2Space R]

theorem P2M_GroundTheory_Heights__Theta_locField_secondCountable_3caae9477f1d (hR : ¬ DiscreteTopology R) : SecondCountableTopology R := by sorry

alias «GroundTheory».«Heights₂».«Theta».«locField_secondCountable» := P2M_GroundTheory_Heights__Theta_locField_secondCountable_3caae9477f1d
