-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_nhdsNE_zero_neBot_71889b9ea3f1
-- name    : P2M_GroundTheory_Heights__Theta_nhdsNE_zero_neBot_71889b9ea3f1
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:54:01.547089+00:00
-- url     : https://prove2.me/theorems/da20d095-8eb3-5254-9c93-c3d34688b3a6
-- title:
--   P2 M Ground Theory Heights  Theta nhds NE zero ne Bot 71889b9ea3f1: P2 M Ground Theory Heights  Theta nhds NE zero ne Bot 71889b9ea3f1
-- statement:
--   The P2 M Ground Theory Heights  Theta nhds NE zero ne Bot 71889b9ea3f1 construction uses the P2 M Ground Theory Heights  Theta nhds NE zero ne Bot 71889b9ea3f1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/LocallyCompactField/Countability.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/LocallyCompactField/Countability.lean#L31-L34

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

theorem P2M_GroundTheory_Heights__Theta_nhdsNE_zero_neBot_71889b9ea3f1 (hR : ¬ DiscreteTopology R) : (𝓝[≠] (0 : R)).NeBot := by sorry

alias «GroundTheory».«Heights₂».«Theta».«nhdsNE_zero_neBot» := P2M_GroundTheory_Heights__Theta_nhdsNE_zero_neBot_71889b9ea3f1
