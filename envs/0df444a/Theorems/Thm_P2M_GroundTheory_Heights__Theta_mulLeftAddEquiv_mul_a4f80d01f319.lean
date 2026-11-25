-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_mulLeftAddEquiv_mul_a4f80d01f319
-- name    : P2M_GroundTheory_Heights__Theta_mulLeftAddEquiv_mul_a4f80d01f319
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:54:02.262807+00:00
-- url     : https://prove2.me/theorems/a7b14495-e5b1-58f8-92a1-a5005b782d40
-- title:
--   P2 M Ground Theory Heights  Theta mul Left Add Equiv mul a4f80d01f319: P2 M Ground Theory Heights  Theta mul Left Add Equiv mul a4f80d01f319
-- statement:
--   The P2 M Ground Theory Heights  Theta mul Left Add Equiv mul a4f80d01f319 construction uses the P2 M Ground Theory Heights  Theta mul Left Add Equiv mul a4f80d01f319 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/LocallyCompactField/Countability.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/LocallyCompactField/Countability.lean#L25-L29

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

theorem P2M_GroundTheory_Heights__Theta_mulLeftAddEquiv_mul_a4f80d01f319 (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) :
    mulLeftAddEquiv (a * b) (mul_ne_zero ha hb) =
      (mulLeftAddEquiv b hb).trans (mulLeftAddEquiv a ha) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«mulLeftAddEquiv_mul» := P2M_GroundTheory_Heights__Theta_mulLeftAddEquiv_mul_a4f80d01f319
