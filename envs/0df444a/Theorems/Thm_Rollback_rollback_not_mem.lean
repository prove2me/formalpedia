-- Prove2me | Theorems.Thm_Rollback_rollback_not_mem
-- name    : Rollback.rollback_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:55:47.909971+00:00
-- url     : https://prove2.me/theorems/772cbaf5-9f33-4626-bd2c-635f278efb11
-- title:
--   Rollback: rollback not mem
-- statement:
--   The Rollback construction uses the rollback not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Rollback.lean#L33-L35
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Rollback.lean#L33-L35

import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Family_Reachability
import Definitions.Def_EventStructures_Family_Rollback
set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
open Rollback

theorem Rollback.rollback_not_mem {c : Conf F} {e : F.Event} {m : Conf F}
    (h : isRollback F c e m) : e ∉ m.1 := by sorry
