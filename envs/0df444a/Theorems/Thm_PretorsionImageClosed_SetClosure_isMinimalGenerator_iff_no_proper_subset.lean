-- Prove2me | Theorems.Thm_PretorsionImageClosed_SetClosure_isMinimalGenerator_iff_no_proper_subset
-- name    : PretorsionImageClosed.SetClosure.isMinimalGenerator_iff_no_proper_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:47:02.783813+00:00
-- url     : https://prove2.me/theorems/fac458ab-4ace-4a59-9146-04c22ecf0f4a
-- title:
--   Set Closure: is Minimal Generator iff no proper subset
-- statement:
--   One-point deletion minimality is equivalent to ordinary
--   inclusion-minimality among generating sets.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Finite.lean#L31-L57
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/Finite.lean#L31-L57

module
public import Mathlib.Data.Set.Card
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Basic
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Finite
set_option autoImplicit true
@[expose] public section
public section
open Set
open PretorsionImageClosed PretorsionImageClosed.SetClosure
variable {E : Type*} {c : SetClosure E}

theorem PretorsionImageClosed.SetClosure.isMinimalGenerator_iff_no_proper_subset
    {B C : Set E} :
    c.IsMinimalGenerator B C ↔
      c B = C ∧ ∀ ⦃D : Set E⦄, D ⊂ B → c D ≠ C := by sorry
