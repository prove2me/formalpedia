-- Prove2me | Theorems.Thm_Trace_traceEquiv_append
-- name    : Trace.traceEquiv_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:48:08.005304+00:00
-- url     : https://prove2.me/theorems/e1185ad1-250b-49cc-a35b-90a37586c65b
-- title:
--   Trace: trace Equiv append
-- statement:
--   Trace equivalence is a congruence for append.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Trace.lean#L117-L119
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Trace.lean#L117-L119

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

theorem Trace.traceEquiv_append {t₁ t₂ t₃ t₄ : List α}
    (h₁ : t₁ ≈ₜ t₂) (h₂ : t₃ ≈ₜ t₄) : (t₁ ++ t₃) ≈ₜ (t₂ ++ t₄) := by sorry
