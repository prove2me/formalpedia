-- Prove2me | Theorems.Thm_PretorsionImageClosed_SetClosure_coe_sup
-- name    : PretorsionImageClosed.SetClosure.coe_sup
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:49:46.120995+00:00
-- url     : https://prove2.me/theorems/ca94ad47-376e-4d72-a231-5a02e397d5d4
-- title:
--   Set Closure: coe sup
-- statement:
--   The Set Closure construction uses the coe sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/ClosedSets.lean#L57-L59
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/ClosedSets.lean#L57-L59

module
public import Mathlib.Order.Grade
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Finite
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_ClosedSets
set_option autoImplicit true
@[expose] public section
public section
open Set
open PretorsionImageClosed PretorsionImageClosed.SetClosure
variable {E : Type*}
variable {c : SetClosure E}

theorem PretorsionImageClosed.SetClosure.coe_sup (C D : c.Closeds) :
    ((C ⊔ D : c.Closeds) : Set E) = c ((C : Set E) ∪ (D : Set E)) := by sorry

attribute [defeq] PretorsionImageClosed.SetClosure.coe_sup
