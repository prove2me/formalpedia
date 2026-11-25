-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_foldr_diffStep_eq_zero_of_mem_e34c1b7dec2b
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_foldr_diffStep_eq_zero_of_mem_e34c1b7dec2b
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:17:21.960565+00:00
-- url     : https://prove2.me/theorems/fc4d6e73-4eee-4f65-beec-c9be10998882
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers foldr diff Step eq zero of mem e34c1b7dec2b: P2 M Ground Theory Heights  Heights Field Numbers foldr diff Step eq zero of mem e34c1b7dec2b
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers foldr diff Step eq zero of mem e34c1b7dec2b construction uses the P2 M Ground Theory Heights  Heights Field Numbers foldr diff Step eq zero of mem e34c1b7dec2b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumZeroSlot.lean#L23-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumZeroSlot.lean#L23-L32

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_foldr_diffStep_eq_zero_of_mem_e34c1b7dec2b (l : List (K → ℤ)) (hl : (0 : K → ℤ) ∈ l)
    (h : (K → ℤ) → ℤ) : l.foldr diffStep h = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«foldr_diffStep_eq_zero_of_mem» := P2M_GroundTheory_Heights__Heights_FieldNumbers_foldr_diffStep_eq_zero_of_mem_e34c1b7dec2b
