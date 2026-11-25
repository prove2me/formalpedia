-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_nat_of_le_of_lt_4b1524a9290b
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_nat_of_le_of_lt_4b1524a9290b
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:17:01.786466+00:00
-- url     : https://prove2.me/theorems/21257ff1-1afc-4020-b540-ccab54c329fd
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers exists nat of le of lt 4b1524a9290b: P2 M Ground Theory Heights  Heights Field Numbers exists nat of le of lt 4b1524a9290b
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers exists nat of le of lt 4b1524a9290b construction uses the P2 M Ground Theory Heights  Heights Field Numbers exists nat of le of lt 4b1524a9290b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumZeroSlot.lean#L63-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumZeroSlot.lean#L63-L74

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_nat_of_le_of_lt_4b1524a9290b {x : WithBot (WithTop ℤ)} {t n : ℕ}
    (h1 : (t : WithBot (WithTop ℤ)) ≤ x) (h2 : x < n) : ∃ d : ℕ, x = d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«exists_nat_of_le_of_lt» := P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_nat_of_le_of_lt_4b1524a9290b
