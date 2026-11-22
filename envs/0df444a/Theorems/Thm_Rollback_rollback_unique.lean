-- Prove2me | Theorems.Thm_Rollback_rollback_unique
-- name    : Rollback.rollback_unique
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T20:56:23.032944+00:00
-- url     : https://prove2.me/theorems/adb36674-4214-44ad-ab3c-06c9726975ff
-- title:
--   Rollback: rollback unique
-- statement:
--   Rollbacks are unique when they exist.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Rollback.lean#L95-L99
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Rollback.lean#L95-L99

import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_Family_Rollback
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Card
import Definitions.Def_EventStructures_Prime_Rollback
set_option autoImplicit true
variable {L : Type*} (es : PES L)
open Rollback
open Configuration ConfFamily
local infix:50 " ⊢ " => enables es

theorem Rollback.rollback_unique {c : Conf es} {e : es.Event}
    {m₁ m₂ : Conf es} (h₁ : isRollback es.toFamily c e m₁) (h₂ : isRollback es.toFamily c e m₂) :
    m₁ = m₂ := by sorry
