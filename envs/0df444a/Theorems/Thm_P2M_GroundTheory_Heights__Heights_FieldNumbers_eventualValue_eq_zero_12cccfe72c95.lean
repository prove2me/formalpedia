-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_eventualValue_eq_zero_12cccfe72c95
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_eventualValue_eq_zero_12cccfe72c95
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:18:49.204548+00:00
-- url     : https://prove2.me/theorems/a7379203-a9e7-4482-bf23-98264161d6cd
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers eventual Value eq zero 12cccfe72c95: P2 M Ground Theory Heights  Heights Field Numbers eventual Value eq zero 12cccfe72c95
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers eventual Value eq zero 12cccfe72c95 construction uses the P2 M Ground Theory Heights  Heights Field Numbers eventual Value eq zero 12cccfe72c95 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumZeroSlot.lean#L53-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumZeroSlot.lean#L53-L59

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_eventualValue_eq_zero_12cccfe72c95 {f : (K → ℤ) → ℤ} (hf : ∀ᶠ m in atTop, f m = 0) :
    eventualValue f = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«eventualValue_eq_zero» := P2M_GroundTheory_Heights__Heights_FieldNumbers_eventualValue_eq_zero_12cccfe72c95
