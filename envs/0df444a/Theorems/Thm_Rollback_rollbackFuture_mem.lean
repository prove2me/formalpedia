-- Prove2me | Theorems.Thm_Rollback_rollbackFuture_mem
-- name    : Rollback.rollbackFuture_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:56:14.656262+00:00
-- url     : https://prove2.me/theorems/48b4586e-072d-4fff-bbfe-bcc3717351e1
-- title:
--   Rollback: rollback Future mem
-- statement:
--   The Rollback construction uses the rollback Future mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Rollback.lean#L47-L49
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Rollback.lean#L47-L49

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

theorem Rollback.rollbackFuture_mem {c : Conf es} {e : es.Event} {x : es.Event} :
    x ∈ (rollbackFuture (es := es) c e).1 ↔ x ∈ c.1 ∧ x ∉ es.future e := by sorry
