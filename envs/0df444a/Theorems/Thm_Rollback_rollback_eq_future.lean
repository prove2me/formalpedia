-- Prove2me | Theorems.Thm_Rollback_rollback_eq_future
-- name    : Rollback.rollback_eq_future
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T20:56:25.595937+00:00
-- url     : https://prove2.me/theorems/035ecad3-6011-4227-8df5-91a5c6092dee
-- title:
--   Rollback: rollback eq future
-- statement:
--   Any rollback coincides with the canonical rollback.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Rollback.lean#L85-L92
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Rollback.lean#L85-L92

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

theorem Rollback.rollback_eq_future {c : Conf es} {e : es.Event} {m : Conf es}
    (h : isRollback es.toFamily c e m) : m.1 = c.1 \ es.future e := by sorry
