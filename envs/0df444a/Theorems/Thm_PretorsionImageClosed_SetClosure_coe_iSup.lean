-- Prove2me | Theorems.Thm_PretorsionImageClosed_SetClosure_coe_iSup
-- name    : PretorsionImageClosed.SetClosure.coe_iSup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:49:17.028796+00:00
-- url     : https://prove2.me/theorems/ab7cee57-dd87-402b-adc4-fc97dd6c4587
-- title:
--   Set Closure: coe i Sup
-- statement:
--   The Set Closure construction uses the coe i Sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/ClosedSets.lean#L62-L64
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/ClosedSets.lean#L62-L64

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

theorem PretorsionImageClosed.SetClosure.coe_iSup {ι : Sort*} (f : ι → c.Closeds) :
    ((⨆ i, f i : c.Closeds) : Set E) = c (⋃ i, (f i : Set E)) := by sorry
