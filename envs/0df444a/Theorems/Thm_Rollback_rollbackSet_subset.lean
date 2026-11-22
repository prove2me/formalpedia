-- Prove2me | Theorems.Thm_Rollback_rollbackSet_subset
-- name    : Rollback.rollbackSet_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:53:56.95046+00:00
-- url     : https://prove2.me/theorems/c0b239b8-5836-4811-8d49-732013a9090a
-- title:
--   Rollback: rollback Set subset
-- statement:
--   The Rollback construction uses the rollback Set subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Rollback.lean#L63-L65
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Rollback.lean#L63-L65

import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Family_Reachability
import Definitions.Def_EventStructures_Family_Rollback
set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
open Rollback

theorem Rollback.rollbackSet_subset (c : Conf F) (e : F.Event) : rollbackSet F c e ⊆ c.val := by sorry
