-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_mixedDiff_update_add_49648a997f11
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_mixedDiff_update_add_49648a997f11
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:19:00.236348+00:00
-- url     : https://prove2.me/theorems/52b23509-9983-436c-b4fc-9e8190a6ce5d
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers mixed Diff update add 49648a997f11: P2 M Ground Theory Heights  Heights Field Numbers mixed Diff update add 49648a997f11
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers mixed Diff update add 49648a997f11 construction uses the P2 M Ground Theory Heights  Heights Field Numbers mixed Diff update add 49648a997f11 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumAdd.lean#L47-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumAdd.lean#L47-L52

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_mixedDiff_update_add_49648a997f11 {n : ℕ} (bs : Fin n → K → ℤ) (i : Fin n) (b b' : K → ℤ)
    (h : (K → ℤ) → ℤ) (m : K → ℤ) :
    mixedDiff (Function.update bs i (b + b')) h m =
      mixedDiff (Function.update bs i b) h m + mixedDiff (Function.update bs i b') h (m - b) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«mixedDiff_update_add» := P2M_GroundTheory_Heights__Heights_FieldNumbers_mixedDiff_update_add_49648a997f11
