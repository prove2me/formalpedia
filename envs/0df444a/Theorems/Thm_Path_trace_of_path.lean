-- Prove2me | Theorems.Thm_Path_trace_of_path
-- name    : Path.trace_of_path
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:00:39.871406+00:00
-- url     : https://prove2.me/theorems/265d69ac-439a-4076-a710-23a5ca253916
-- title:
--   Path: trace of path
-- statement:
--   Events executed in a path must be added to reach the target configuration.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Path.lean#L321-L335
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Path.lean#L321-L335

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

theorem Path.trace_of_path {c₁ c₂ : Conf F} (p : Path F c₁ c₂) :
    ∀ e ∈ trace F p, e ∈ c₂.1 := by sorry
