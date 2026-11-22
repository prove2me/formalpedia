-- Prove2me | Theorems.Thm_PES_past_conflict_free
-- name    : PES.past_conflict_free
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T20:47:03.948817+00:00
-- url     : https://prove2.me/theorems/ffba76d4-c9d1-4a92-8902-93e30ce7a6c7
-- title:
--   PES: past conflict free
-- statement:
--   The past of any event is conflict-free.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Basic.lean#L90-L93
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Basic.lean#L90-L93

import Mathlib.Order.Basic
import Mathlib.Data.Set.Finite.Basic
import Definitions.Def_EventStructures_Prime_Basic
set_option autoImplicit true
open PES
variable {L : Type*} (es : PES L)
local infixl:50 " # " => es.conflict
local infixl:50 " ⋈ " => es.concurrent
local infixl:50 " ## " => es.minimalConflict

theorem PES.past_conflict_free {e e₁ e₂ : es.Event}
    (h₁ : e₁ ≤ e) (h₂ : e₂ ≤ e) : ¬ es.conflict e₁ e₂ := by sorry
