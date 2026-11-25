-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ofFn_update_64c49455c3c2
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_ofFn_update_64c49455c3c2
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:18:48.118204+00:00
-- url     : https://prove2.me/theorems/95b32953-9e03-57b5-b7d2-a4c614e27b0d
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers of Fn update 64c49455c3c2: P2 M Ground Theory Heights  Heights Field Numbers of Fn update 64c49455c3c2
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers of Fn update 64c49455c3c2 construction uses the P2 M Ground Theory Heights  Heights Field Numbers of Fn update 64c49455c3c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumAdd.lean#L35-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumAdd.lean#L35-L45

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_ofFn_update_64c49455c3c2 {α : Type*} {n : ℕ} (bs : Fin n → α) (i : Fin n) (x : α) :
    List.ofFn (Function.update bs i x) = (List.ofFn bs).set i x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«ofFn_update» := P2M_GroundTheory_Heights__Heights_FieldNumbers_ofFn_update_64c49455c3c2
