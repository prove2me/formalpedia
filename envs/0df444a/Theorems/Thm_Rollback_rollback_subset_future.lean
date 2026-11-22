-- Prove2me | Theorems.Thm_Rollback_rollback_subset_future
-- name    : Rollback.rollback_subset_future
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T20:55:57.515812+00:00
-- url     : https://prove2.me/theorems/ef5a969a-d0e5-47d9-86b4-cd1048a3bc63
-- title:
--   Rollback: rollback subset future
-- statement:
--   The Rollback construction uses the rollback subset future property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Rollback.lean#L15-L22
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Rollback.lean#L15-L22

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

theorem Rollback.rollback_subset_future {c : Conf es} {e : es.Event} {m : Conf es}
    (h : isRollback es.toFamily c e m) : m.1 ⊆ c.1 \ es.future e := by sorry
