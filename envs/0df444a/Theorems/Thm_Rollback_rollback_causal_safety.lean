-- Prove2me | Theorems.Thm_Rollback_rollback_causal_safety
-- name    : Rollback.rollback_causal_safety
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:02:19.365914+00:00
-- url     : https://prove2.me/theorems/3b572809-db75-499c-8e2b-121d35cb7691
-- title:
--   Rollback: rollback causal safety
-- statement:
--   Causal safety: Rollback removes exactly the causal consequences of `e`.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Rollback.lean#L67-L69
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Rollback.lean#L67-L69

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

theorem Rollback.rollback_causal_safety {c : Conf es} {e : es.Event} {x : es.Event} :
    x ∈ (rollbackFuture (es := es) c e).1 → x ∉ es.future e := by sorry
