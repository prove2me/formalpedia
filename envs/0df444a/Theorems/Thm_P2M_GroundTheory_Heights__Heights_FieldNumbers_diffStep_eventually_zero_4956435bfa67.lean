-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_diffStep_eventually_zero_4956435bfa67
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_diffStep_eventually_zero_4956435bfa67
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:18:20.309931+00:00
-- url     : https://prove2.me/theorems/b0a53afc-c9fe-58d3-8d8c-30cc11a17332
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers diff Step eventually zero 4956435bfa67: P2 M Ground Theory Heights  Heights Field Numbers diff Step eventually zero 4956435bfa67
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers diff Step eventually zero 4956435bfa67 construction uses the P2 M Ground Theory Heights  Heights Field Numbers diff Step eventually zero 4956435bfa67 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumZeroSlot.lean#L38-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumZeroSlot.lean#L38-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumZeroSlot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open GroundTheory.Heights₂.Heights.NumbersDVR Filter
universe u
variable {K : Type*}

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_diffStep_eventually_zero_4956435bfa67 {b : K → ℤ} {h : (K → ℤ) → ℤ}
    (hh : ∀ᶠ m in atTop, h m = 0) : ∀ᶠ m in atTop, diffStep b h m = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«diffStep_eventually_zero» := P2M_GroundTheory_Heights__Heights_FieldNumbers_diffStep_eventually_zero_4956435bfa67
