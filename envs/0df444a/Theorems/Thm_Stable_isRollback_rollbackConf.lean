-- Prove2me | Theorems.Thm_Stable_isRollback_rollbackConf
-- name    : Stable.isRollback_rollbackConf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:03:54.514808+00:00
-- url     : https://prove2.me/theorems/d5da7cba-9e7e-4be6-8a4b-baaf9028db24
-- title:
--   Stable: is Rollback rollback Conf
-- statement:
--   Hence it is a rollback.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Rollback.lean#L32-L35
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Rollback.lean#L32-L35

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Family_Rollback
import Definitions.Def_EventStructures_Stable_Rollback
set_option autoImplicit true
open ConfFamily Rollback
variable {L : Type*} {F : ConfFamily L}
open Stable

theorem Stable.isRollback_rollbackConf (hF : Coherent F) (c : Conf F) (e : F.Event) :
    isRollback F c e (rollbackConf hF c e) := by sorry
