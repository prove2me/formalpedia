-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_locField_nhds_zero_isCountablyGenerated_63767aaca2c3
-- name    : P2M_GroundTheory_Heights__Theta_locField_nhds_zero_isCountablyGenerated_63767aaca2c3
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:53:52.49699+00:00
-- url     : https://prove2.me/theorems/6582509e-3e13-4ee5-90dd-2d8581d15659
-- title:
--   P2 M Ground Theory Heights  Theta loc Field nhds zero is Countably Generated 63767aaca2c3: P2 M Ground Theory Heights  Theta loc Field nhds zero is Countably Generated 63767aaca2c3
-- statement:
--   The P2 M Ground Theory Heights  Theta loc Field nhds zero is Countably Generated 63767aaca2c3 construction uses the P2 M Ground Theory Heights  Theta loc Field nhds zero is Countably Generated 63767aaca2c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/LocallyCompactField/Countability.lean#L174-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/LocallyCompactField/Countability.lean#L174-L190

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

theorem P2M_GroundTheory_Heights__Theta_locField_nhds_zero_isCountablyGenerated_63767aaca2c3 (hR : ¬ DiscreteTopology R) :
    (𝓝 (0 : R)).IsCountablyGenerated := by sorry

alias «GroundTheory».«Heights₂».«Theta».«locField_nhds_zero_isCountablyGenerated» := P2M_GroundTheory_Heights__Theta_locField_nhds_zero_isCountablyGenerated_63767aaca2c3
