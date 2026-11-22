-- Prove2me | Theorems.Thm_Rollback_rollback_maximal
-- name    : Rollback.rollback_maximal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:01:33.141904+00:00
-- url     : https://prove2.me/theorems/c8e24ae2-d15d-4349-913e-2e4d7a0be136
-- title:
--   Rollback: rollback maximal
-- statement:
--   The Rollback construction uses the rollback maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Rollback.lean#L37-L40
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Rollback.lean#L37-L40

import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Family_Reachability
import Definitions.Def_EventStructures_Family_Rollback
set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
open Rollback

theorem Rollback.rollback_maximal {c : Conf F} {e : F.Event} {m : Conf F}
    (h : isRollback F c e m) :
    ∀ m' : Conf F, m'.1 ⊆ c.1 → e ∉ m'.1 → m.1 ⊆ m'.1 → m'.1 ⊆ m.1 := by sorry
