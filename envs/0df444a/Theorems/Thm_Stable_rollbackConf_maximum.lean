-- Prove2me | Theorems.Thm_Stable_rollbackConf_maximum
-- name    : Stable.rollbackConf_maximum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:03:56.443808+00:00
-- url     : https://prove2.me/theorems/d260dcb3-18ab-4950-b7b1-3707bc7d4484
-- title:
--   Stable: rollback Conf maximum
-- statement:
--   It is the greatest subconfiguration of `c` omitting `e`.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Rollback.lean#L26-L29
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Rollback.lean#L26-L29

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Family_Rollback
import Definitions.Def_EventStructures_Stable_Rollback
set_option autoImplicit true
open ConfFamily Rollback
variable {L : Type*} {F : ConfFamily L}
open Stable

theorem Stable.rollbackConf_maximum (hF : Coherent F) (c : Conf F) (e : F.Event)
    (m : Conf F) (hmc : m.val ⊆ c.val) (hem : e ∉ m.val) :
    m.val ⊆ (rollbackConf hF c e).val := by sorry
