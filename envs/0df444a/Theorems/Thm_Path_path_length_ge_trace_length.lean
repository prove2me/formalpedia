-- Prove2me | Theorems.Thm_Path_path_length_ge_trace_length
-- name    : Path.path_length_ge_trace_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:00:45.110362+00:00
-- url     : https://prove2.me/theorems/cae01380-cca6-4c5b-b002-60197b6b4ad7
-- title:
--   Path: path length ge trace length
-- statement:
--   A path requires executing at least the events in its trace.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Path.lean#L338-L340
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Path.lean#L338-L340

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

theorem Path.path_length_ge_trace_length {c₁ c₂ : Conf F} (p : Path F c₁ c₂) :
    length F p = (trace F p).length := by sorry
