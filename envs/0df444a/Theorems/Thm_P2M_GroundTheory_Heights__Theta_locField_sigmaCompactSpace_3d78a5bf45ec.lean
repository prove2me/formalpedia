-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_locField_sigmaCompactSpace_3d78a5bf45ec
-- name    : P2M_GroundTheory_Heights__Theta_locField_sigmaCompactSpace_3d78a5bf45ec
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:53:53.850151+00:00
-- url     : https://prove2.me/theorems/0065ee08-6bb6-4704-8304-55c856fe2d4d
-- title:
--   P2 M Ground Theory Heights  Theta loc Field sigma Compact Space 3d78a5bf45ec: P2 M Ground Theory Heights  Theta loc Field sigma Compact Space 3d78a5bf45ec
-- statement:
--   The P2 M Ground Theory Heights  Theta loc Field sigma Compact Space 3d78a5bf45ec construction uses the P2 M Ground Theory Heights  Theta loc Field sigma Compact Space 3d78a5bf45ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/LocallyCompactField/Countability.lean#L161-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/LocallyCompactField/Countability.lean#L161-L172

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

theorem P2M_GroundTheory_Heights__Theta_locField_sigmaCompactSpace_3d78a5bf45ec (hR : ¬ DiscreteTopology R) : SigmaCompactSpace R := by sorry

alias «GroundTheory».«Heights₂».«Theta».«locField_sigmaCompactSpace» := P2M_GroundTheory_Heights__Theta_locField_sigmaCompactSpace_3d78a5bf45ec
