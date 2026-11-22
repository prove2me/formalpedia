-- Prove2me | Theorems.Thm_Path_trace_length_eq_length
-- name    : Path.trace_length_eq_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:00:29.018078+00:00
-- url     : https://prove2.me/theorems/e6009ba3-9bfa-4940-8ca2-7f370e861625
-- title:
--   Path: trace length eq length
-- statement:
--   For a path from c₁ to c₂, every event in the trace appears exactly once.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Path.lean#L305-L307
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Path.lean#L305-L307

import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Family_Trace
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Nat.Find
import Definitions.Def_EventStructures_Family_Path
set_option autoImplicit true
variable {L : Type*} (F : ConfFamily L)
open ConfFamily
local infix:50 " ⊢ " => enables F
open Path
local infixr:60 " ≈ₚ " => PathEquiv F

theorem Path.trace_length_eq_length {c₁ c₂ : Conf F} (p : Path F c₁ c₂) :
    (trace F p).length = length F p := by sorry
