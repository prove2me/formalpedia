-- Prove2me | Theorems.Thm_Rollback_rollback_subset
-- name    : Rollback.rollback_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:55:49.183731+00:00
-- url     : https://prove2.me/theorems/eb885345-d02b-408f-9f33-abc34119ab90
-- title:
--   Rollback: rollback subset
-- statement:
--   The Rollback construction uses the rollback subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Rollback.lean#L29-L31
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Rollback.lean#L29-L31

import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Family_Reachability
import Definitions.Def_EventStructures_Family_Rollback
set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
open Rollback

theorem Rollback.rollback_subset {c : Conf F} {e : F.Event} {m : Conf F}
    (h : isRollback F c e m) : m.1 ⊆ c.1 := by sorry
