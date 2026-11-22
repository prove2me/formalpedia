-- Prove2me | Theorems.Thm_Rollback_rollback_correctness_finite
-- name    : Rollback.rollback_correctness_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:02:30.963084+00:00
-- url     : https://prove2.me/theorems/65dc99ec-80c4-4621-a047-06917db7955a
-- title:
--   Rollback: rollback correctness finite
-- statement:
--   Correctness: `c` is reachable from `rollback(c,e)` when `c` is finite.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Rollback.lean#L114-L119
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Rollback.lean#L114-L119

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

theorem Rollback.rollback_correctness_finite {c : Conf es} {e : es.Event}
    (cF : Finset es.Event) (hcF : ∀ x, x ∈ cF ↔ x ∈ c.1) :
    Nonempty (Path es.toFamily (rollbackFuture (es := es) c e) c) := by sorry
