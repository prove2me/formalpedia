-- Prove2me | Theorems.Thm_Trace_labels_swap_iff
-- name    : Trace.labels_swap_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:42:38.616228+00:00
-- url     : https://prove2.me/theorems/f247d345-36cc-42d8-9062-c1f7b2493951
-- title:
--   Trace: labels swap iff
-- statement:
--   Swapping two adjacent events preserves the label sequence iff they share a label.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Trace.lean#L44-L54
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Trace.lean#L44-L54

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

theorem Trace.labels_swap_iff {e₁ e₂ : α} {t₁ t₂ : List α} :
    labels lbl (t₁ ++ e₁ :: e₂ :: t₂) = labels lbl (t₁ ++ e₂ :: e₁ :: t₂) ↔
    lbl e₁ = lbl e₂ := by sorry
