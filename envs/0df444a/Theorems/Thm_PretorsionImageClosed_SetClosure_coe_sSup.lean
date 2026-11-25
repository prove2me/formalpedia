-- Prove2me | Theorems.Thm_PretorsionImageClosed_SetClosure_coe_sSup
-- name    : PretorsionImageClosed.SetClosure.coe_sSup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:51:34.065615+00:00
-- url     : https://prove2.me/theorems/93d53718-3b02-4618-add8-b08e26243759
-- title:
--   Set Closure: coe s Sup
-- statement:
--   The Set Closure construction uses the coe s Sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/ClosedSets.lean#L72-L75
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/ClosedSets.lean#L72-L75

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

theorem PretorsionImageClosed.SetClosure.coe_sSup (S : Set c.Closeds) :
    ((sSup S : c.Closeds) : Set E) =
      c (⋃ C : S, (C.1 : Set E)) := by sorry
