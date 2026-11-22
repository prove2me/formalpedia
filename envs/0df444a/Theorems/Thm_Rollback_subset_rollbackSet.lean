-- Prove2me | Theorems.Thm_Rollback_subset_rollbackSet
-- name    : Rollback.subset_rollbackSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:53:34.633852+00:00
-- url     : https://prove2.me/theorems/a96f424e-c409-480a-bc8a-ba8138a0d91a
-- title:
--   Rollback: subset rollback Set
-- statement:
--   The Rollback construction uses the subset rollback Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Rollback.lean#L71-L73
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Rollback.lean#L71-L73

import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Family_Reachability
import Definitions.Def_EventStructures_Family_Rollback
set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
open Rollback

theorem Rollback.subset_rollbackSet {c m : Conf F} {e : F.Event}
    (hmc : m.val ⊆ c.val) (hem : e ∉ m.val) : m.val ⊆ rollbackSet F c e := by sorry
