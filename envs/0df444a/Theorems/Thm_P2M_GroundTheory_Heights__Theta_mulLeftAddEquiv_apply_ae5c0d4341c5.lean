-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_mulLeftAddEquiv_apply_ae5c0d4341c5
-- name    : P2M_GroundTheory_Heights__Theta_mulLeftAddEquiv_apply_ae5c0d4341c5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:39:07.974802+00:00
-- url     : https://prove2.me/theorems/33143bf0-2ec2-4479-a6f8-1ddd3d375599
-- title:
--   P2 M Ground Theory Heights  Theta mul Left Add Equiv apply ae5c0d4341c5: P2 M Ground Theory Heights  Theta mul Left Add Equiv apply ae5c0d4341c5
-- statement:
--   The P2 M Ground Theory Heights  Theta mul Left Add Equiv apply ae5c0d4341c5 construction uses the P2 M Ground Theory Heights  Theta mul Left Add Equiv apply ae5c0d4341c5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/LocallyCompactField/Countability.lean#L23-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/LocallyCompactField/Countability.lean#L23-L23

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

theorem P2M_GroundTheory_Heights__Theta_mulLeftAddEquiv_apply_ae5c0d4341c5 (a : R) (ha : a ≠ 0) (x : R) : mulLeftAddEquiv a ha x = a * x := by sorry

alias «GroundTheory».«Heights₂».«Theta».«mulLeftAddEquiv_apply» := P2M_GroundTheory_Heights__Theta_mulLeftAddEquiv_apply_ae5c0d4341c5
