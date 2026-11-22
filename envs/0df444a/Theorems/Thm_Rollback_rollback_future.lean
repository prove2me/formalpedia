-- Prove2me | Theorems.Thm_Rollback_rollback_future
-- name    : Rollback.rollback_future
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:56:14.200505+00:00
-- url     : https://prove2.me/theorems/21dc95ad-3702-4784-af99-84dde606530e
-- title:
--   Rollback: rollback future
-- statement:
--   The canonical rollback is a rollback for `c` and `e`.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Rollback.lean#L72-L82
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Rollback.lean#L72-L82

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

theorem Rollback.rollback_future {c : Conf es} {e : es.Event} :
    isRollback es.toFamily c e (rollbackFuture (es := es) c e) := by sorry
