-- Prove2me | Theorems.Thm_Rollback_rollbackFuture_val
-- name    : Rollback.rollbackFuture_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:56:12.830118+00:00
-- url     : https://prove2.me/theorems/6f6b5e61-4d31-4ff1-a14a-20db1c640f5b
-- title:
--   Rollback: rollback Future val
-- statement:
--   The Rollback construction uses the rollback Future val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Rollback.lean#L43-L45
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Rollback.lean#L43-L45

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

theorem Rollback.rollbackFuture_val (c : Conf es) (e : es.Event) :
    (rollbackFuture (es := es) c e).1 = c.1 \ es.future e := by sorry

attribute [defeq] Rollback.rollbackFuture_val
