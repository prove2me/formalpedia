-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_mixedDiff_coord_zero_b5ada36f56e1
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_mixedDiff_coord_zero_b5ada36f56e1
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:17:15.079699+00:00
-- url     : https://prove2.me/theorems/e29ff7f6-e344-44bb-919d-b871a301a139
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers mixed Diff coord zero b5ada36f56e1: P2 M Ground Theory Heights  Heights Field Numbers mixed Diff coord zero b5ada36f56e1
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers mixed Diff coord zero b5ada36f56e1 construction uses the P2 M Ground Theory Heights  Heights Field Numbers mixed Diff coord zero b5ada36f56e1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumZeroSlot.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumZeroSlot.lean#L34-L36

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_mixedDiff_coord_zero_b5ada36f56e1 {n : ℕ} (bs : Fin n → K → ℤ) (i : Fin n) (hi : bs i = 0)
    (h : (K → ℤ) → ℤ) : mixedDiff bs h = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«mixedDiff_coord_zero» := P2M_GroundTheory_Heights__Heights_FieldNumbers_mixedDiff_coord_zero_b5ada36f56e1
