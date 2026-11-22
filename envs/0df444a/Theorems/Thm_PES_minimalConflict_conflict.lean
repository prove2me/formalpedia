-- Prove2me | Theorems.Thm_PES_minimalConflict_conflict
-- name    : PES.minimalConflict_conflict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:46:30.126791+00:00
-- url     : https://prove2.me/theorems/4f19bb64-7ba5-4329-b755-e8e15d5ffa6e
-- title:
--   PES: minimal Conflict conflict
-- statement:
--   If (e₁, e₂) are in minimal conflict, then e₁ and e₂ conflict.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Basic.lean#L73-L75
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Basic.lean#L73-L75

import Mathlib.Order.Basic
import Mathlib.Data.Set.Finite.Basic
import Definitions.Def_EventStructures_Prime_Basic
set_option autoImplicit true
open PES
variable {L : Type*} (es : PES L)
local infixl:50 " # " => es.conflict
local infixl:50 " ⋈ " => es.concurrent
local infixl:50 " ## " => es.minimalConflict

theorem PES.minimalConflict_conflict {e₁ e₂ : es.Event} (h : es.minimalConflict e₁ e₂) :
    es.conflict e₁ e₂ := by sorry
