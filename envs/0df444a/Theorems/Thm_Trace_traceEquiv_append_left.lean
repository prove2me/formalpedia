-- Prove2me | Theorems.Thm_Trace_traceEquiv_append_left
-- name    : Trace.traceEquiv_append_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:42:36.604236+00:00
-- url     : https://prove2.me/theorems/0997cd79-3644-4b8d-adf1-36fb05d987b3
-- title:
--   Trace: trace Equiv append left
-- statement:
--   Trace equivalence is a left congruence for append.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Trace.lean#L93-L102
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Trace.lean#L93-L102

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

theorem Trace.traceEquiv_append_left {t₁ t₂ : List α} (h : t₁ ≈ₜ t₂) (t : List α) :
    (t ++ t₁) ≈ₜ (t ++ t₂) := by sorry
