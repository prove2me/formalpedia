-- Prove2me | Theorems.Thm_Path_pathEquivEquivalence
-- name    : Path.pathEquivEquivalence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:00:13.928459+00:00
-- url     : https://prove2.me/theorems/5428a922-c4e7-4785-8d2d-eb69e4833f67
-- title:
--   Path: path Equiv Equivalence
-- statement:
--   Path equivalence is an equivalence relation.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Path.lean#L229-L233
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Path.lean#L229-L233

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

theorem Path.pathEquivEquivalence (c₁ c₂ : Conf F) :
    Equivalence (PathEquiv (F := F) (c₁ := c₁) (c₂ := c₂)) := by sorry
