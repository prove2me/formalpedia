-- Prove2me | Theorems.Thm_PES_concurrent_irrefl
-- name    : PES.concurrent_irrefl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:39:10.009802+00:00
-- url     : https://prove2.me/theorems/0a2e7337-4de1-466c-8d85-c262d850059b
-- title:
--   PES: concurrent irrefl
-- statement:
--   Concurrency is irreflexive.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Basic.lean#L43-L44
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Basic.lean#L43-L44

import Mathlib.Order.Basic
import Mathlib.Data.Set.Finite.Basic
import Definitions.Def_EventStructures_Prime_Basic
set_option autoImplicit true
open PES
variable {L : Type*} (es : PES L)
local infixl:50 " # " => es.conflict
local infixl:50 " ⋈ " => es.concurrent

theorem PES.concurrent_irrefl : ∀ e, ¬ es.concurrent e e := by sorry
