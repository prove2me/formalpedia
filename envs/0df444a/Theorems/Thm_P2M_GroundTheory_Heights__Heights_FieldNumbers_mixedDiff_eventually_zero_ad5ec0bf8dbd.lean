-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_mixedDiff_eventually_zero_ad5ec0bf8dbd
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_mixedDiff_eventually_zero_ad5ec0bf8dbd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:17:25.292454+00:00
-- url     : https://prove2.me/theorems/b1f1e945-8494-4396-8354-54c7c7e273ab
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers mixed Diff eventually zero ad5ec0bf8dbd: P2 M Ground Theory Heights  Heights Field Numbers mixed Diff eventually zero ad5ec0bf8dbd
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers mixed Diff eventually zero ad5ec0bf8dbd construction uses the P2 M Ground Theory Heights  Heights Field Numbers mixed Diff eventually zero ad5ec0bf8dbd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumZeroSlot.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumZeroSlot.lean#L46-L51

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_mixedDiff_eventually_zero_ad5ec0bf8dbd {n : ℕ} (bs : Fin n → K → ℤ) {h : (K → ℤ) → ℤ}
    (hh : ∀ᶠ m in atTop, h m = 0) : ∀ᶠ m in atTop, mixedDiff bs h m = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«mixedDiff_eventually_zero» := P2M_GroundTheory_Heights__Heights_FieldNumbers_mixedDiff_eventually_zero_ad5ec0bf8dbd
