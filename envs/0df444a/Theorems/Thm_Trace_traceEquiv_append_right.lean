-- Prove2me | Theorems.Thm_Trace_traceEquiv_append_right
-- name    : Trace.traceEquiv_append_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:43:15.627364+00:00
-- url     : https://prove2.me/theorems/ca6f96fb-bb16-4a8d-9f3a-c3d5de41d477
-- title:
--   Trace: trace Equiv append right
-- statement:
--   Trace equivalence is a right congruence for append.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Trace.lean#L105-L114
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Trace.lean#L105-L114

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Basic
import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Family_Trace
set_option autoImplicit true
variable {α L : Type*} (R : α → α → Prop) (lbl : α → L)
local infixr:60 " ≈ₜ " => TraceEquiv R
open Trace

theorem Trace.traceEquiv_append_right {t₁ t₂ : List α} (h : t₁ ≈ₜ t₂) (t : List α) :
    (t₁ ++ t) ≈ₜ (t₂ ++ t) := by sorry
