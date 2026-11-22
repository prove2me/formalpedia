-- Prove2me | Theorems.Thm_Path_path_subset
-- name    : Path.path_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:52:43.891965+00:00
-- url     : https://prove2.me/theorems/c5f5a2e6-8f2e-4c3b-8de0-f48a5bc6b741
-- title:
--   Path: path subset
-- statement:
--   Paths are monotone: the source configuration is a subset of the target.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Path.lean#L310-L318
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Path.lean#L310-L318

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

theorem Path.path_subset {c₁ c₂ : Conf F} (p : Path F c₁ c₂) : c₁.1 ⊆ c₂.1 := by sorry
