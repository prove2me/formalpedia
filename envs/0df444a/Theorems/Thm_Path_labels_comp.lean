-- Prove2me | Theorems.Thm_Path_labels_comp
-- name    : Path.labels_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:00:16.398606+00:00
-- url     : https://prove2.me/theorems/e3bda458-ceb1-47cf-af7d-79816f866239
-- title:
--   Path: labels comp
-- statement:
--   Path labels are concatenated under path composition.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Path.lean#L245-L247
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Path.lean#L245-L247

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

theorem Path.labels_comp {c₁ c₂ c₃ : Conf F} (p₁₂ : Path F c₁ c₂) (p₂₃ : Path F c₂ c₃) :
    labels F (path_comp F p₁₂ p₂₃) = labels F p₁₂ ++ labels F p₂₃ := by sorry
