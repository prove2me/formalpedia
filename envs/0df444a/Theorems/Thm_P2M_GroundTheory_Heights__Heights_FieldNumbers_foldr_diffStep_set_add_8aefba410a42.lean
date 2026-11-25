-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_foldr_diffStep_set_add_8aefba410a42
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_foldr_diffStep_set_add_8aefba410a42
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:18:31.708732+00:00
-- url     : https://prove2.me/theorems/9a190651-564d-5856-b38d-5f7fa5533332
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers foldr diff Step set add 8aefba410a42: P2 M Ground Theory Heights  Heights Field Numbers foldr diff Step set add 8aefba410a42
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers foldr diff Step set add 8aefba410a42 construction uses the P2 M Ground Theory Heights  Heights Field Numbers foldr diff Step set add 8aefba410a42 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumAdd.lean#L20-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumAdd.lean#L20-L33

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_foldr_diffStep_set_add_8aefba410a42 (h : (K → ℤ) → ℤ) (b b' : K → ℤ) :
    ∀ (L : List (K → ℤ)) (i : ℕ), i < L.length → ∀ m : K → ℤ,
      (L.set i (b + b')).foldr diffStep h m =
        (L.set i b).foldr diffStep h m + (L.set i b').foldr diffStep h (m - b)
  := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«foldr_diffStep_set_add» := P2M_GroundTheory_Heights__Heights_FieldNumbers_foldr_diffStep_set_add_8aefba410a42
