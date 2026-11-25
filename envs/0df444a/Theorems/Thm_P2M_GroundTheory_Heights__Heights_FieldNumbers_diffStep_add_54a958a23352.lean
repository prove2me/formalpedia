-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_diffStep_add_54a958a23352
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_diffStep_add_54a958a23352
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:17:17.93269+00:00
-- url     : https://prove2.me/theorems/1a1ca8ba-1887-42a9-9d4c-3eedc9065b81
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers diff Step add 54a958a23352: P2 M Ground Theory Heights  Heights Field Numbers diff Step add 54a958a23352
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers diff Step add 54a958a23352 construction uses the P2 M Ground Theory Heights  Heights Field Numbers diff Step add 54a958a23352 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumAdd.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumAdd.lean#L15-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumAdd
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
open GroundTheory.Heights₂.Heights.NumbersDVR
universe u
variable {K : Type*}

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_diffStep_add_54a958a23352 (b b' : K → ℤ) (h : (K → ℤ) → ℤ) (m : K → ℤ) :
    diffStep (b + b') h m = diffStep b h m + diffStep b' h (m - b) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«diffStep_add» := P2M_GroundTheory_Heights__Heights_FieldNumbers_diffStep_add_54a958a23352
