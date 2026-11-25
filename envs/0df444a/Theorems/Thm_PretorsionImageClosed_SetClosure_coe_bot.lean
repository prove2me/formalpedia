-- Prove2me | Theorems.Thm_PretorsionImageClosed_SetClosure_coe_bot
-- name    : PretorsionImageClosed.SetClosure.coe_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:49:31.842846+00:00
-- url     : https://prove2.me/theorems/bb29395b-434f-568d-acbc-f848d2942365
-- title:
--   Set Closure: coe bot
-- statement:
--   The Set Closure construction uses the coe bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/ClosedSets.lean#L42-L44
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/ClosedSets.lean#L42-L44

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

theorem PretorsionImageClosed.SetClosure.coe_bot (c : SetClosure E) :
    ((⊥ : c.Closeds) : Set E) = c ∅ := by sorry

attribute [defeq] PretorsionImageClosed.SetClosure.coe_bot
