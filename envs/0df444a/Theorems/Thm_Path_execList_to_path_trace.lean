-- Prove2me | Theorems.Thm_Path_execList_to_path_trace
-- name    : Path.execList_to_path_trace
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T20:59:36.825237+00:00
-- url     : https://prove2.me/theorems/6f541406-0fcb-4e4a-8dfb-8b5d39d6a1d3
-- title:
--   Path: exec List to path trace
-- statement:
--   The trace of an execList_to_path is exactly the original list.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Path.lean#L177-L180
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Path.lean#L177-L180

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

theorem Path.execList_to_path_trace {c₁ c₂ : Conf F} {t : List F.Event}
    (h : ExecList F c₁ t c₂) :
    trace F (execList_to_path (F := F) h) = t := by sorry
