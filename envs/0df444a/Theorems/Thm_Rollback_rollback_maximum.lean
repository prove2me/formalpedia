-- Prove2me | Theorems.Thm_Rollback_rollback_maximum
-- name    : Rollback.rollback_maximum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:02:35.582637+00:00
-- url     : https://prove2.me/theorems/138ff024-80cb-4715-bc22-8cefde93e23f
-- title:
--   Rollback: rollback maximum
-- statement:
--   The rollback is the maximum element among rollback candidates.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Rollback.lean#L102-L111
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Rollback.lean#L102-L111

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

theorem Rollback.rollback_maximum {c : Conf es} {e : es.Event} {m : Conf es}
    (h : isRollback es.toFamily c e m) :
    ∀ m' : Conf es, m' ∈ RollbackCandidates es.toFamily c e → m'.1 ⊆ m.1 := by sorry
