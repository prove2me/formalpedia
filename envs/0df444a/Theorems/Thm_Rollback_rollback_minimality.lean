-- Prove2me | Theorems.Thm_Rollback_rollback_minimality
-- name    : Rollback.rollback_minimality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:02:51.620816+00:00
-- url     : https://prove2.me/theorems/9fce5347-f01b-4275-bb0e-fe8444661344
-- title:
--   Rollback: rollback minimality
-- statement:
--   Any path from a redo candidate `c'` to `c` is at least as long as the
--   number of events of `c` causally after `e`.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Rollback.lean#L124-L146
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Rollback.lean#L124-L146

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
set_option linter.unusedDecidableInType false

theorem Rollback.rollback_minimality [DecidableEq es.Event] {c : Conf es} {e : es.Event}
    {c' : Conf es} (_hredo : c'.1 ⊢ e) (hsafe : ∀ x ∈ c'.1, x ∉ es.future e)
    (p' : Path es.toFamily c' c) :
    (c.1 ∩ es.future e).ncard ≤ Path.length es.toFamily p' := by sorry
