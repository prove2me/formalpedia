-- Prove2me | Theorems.Thm_Stable_rollback_unique
-- name    : Stable.rollback_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:03:55.926136+00:00
-- url     : https://prove2.me/theorems/dfe8d486-aba3-4926-8825-64f42709eee1
-- title:
--   Stable: rollback unique
-- statement:
--   Rollbacks are unique: any rollback is the rollback set.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Rollback.lean#L38-L43
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Rollback.lean#L38-L43

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Family_Rollback
import Definitions.Def_EventStructures_Stable_Rollback
set_option autoImplicit true
open ConfFamily Rollback
variable {L : Type*} {F : ConfFamily L}
open Stable

theorem Stable.rollback_unique (hF : Coherent F) {c : Conf F} {e : F.Event} {m : Conf F}
    (h : isRollback F c e m) : m = rollbackConf hF c e := by sorry
