-- Prove2me | Theorems.Thm_Rollback_rollback_redoable
-- name    : Rollback.rollback_redoable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:02:13.185521+00:00
-- url     : https://prove2.me/theorems/a469f632-c350-47f8-a1d0-f69641d8bd7a
-- title:
--   Rollback: rollback redoable
-- statement:
--   Redoability: `e` is enabled in `rollback(c,e)` when `e ∈ c`.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Rollback.lean#L52-L64
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Rollback.lean#L52-L64

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

theorem Rollback.rollback_redoable {c : Conf es} {e : es.Event} (he : e ∈ c.1) :
    (rollbackFuture (es := es) c e).1 ⊢ e := by sorry
