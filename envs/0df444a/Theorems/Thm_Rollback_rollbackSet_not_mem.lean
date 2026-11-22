-- Prove2me | Theorems.Thm_Rollback_rollbackSet_not_mem
-- name    : Rollback.rollbackSet_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:53:59.138848+00:00
-- url     : https://prove2.me/theorems/dee7fddd-12fd-458f-8e86-0b074b471d56
-- title:
--   Rollback: rollback Set not mem
-- statement:
--   The Rollback construction uses the rollback Set not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Rollback.lean#L67-L69
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Rollback.lean#L67-L69

import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Family_Reachability
import Definitions.Def_EventStructures_Family_Rollback
set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
open Rollback

theorem Rollback.rollbackSet_not_mem (c : Conf F) (e : F.Event) : e ∉ rollbackSet F c e := by sorry
