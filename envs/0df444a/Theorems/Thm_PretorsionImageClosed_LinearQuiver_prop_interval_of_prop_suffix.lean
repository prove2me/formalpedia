-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_prop_interval_of_prop_suffix
-- name    : PretorsionImageClosed.LinearQuiver.prop_interval_of_prop_suffix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:10:58.163713+00:00
-- url     : https://prove2.me/theorems/77867ac4-56f8-56f6-92a7-b7ab55f8571f
-- title:
--   Linear Quiver: prop interval of prop suffix
-- statement:
--   The underlying object of the suffix subobject `M_{c,b}` of `M_{a,b}`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/ImageClosed.lean#L45-L48
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/ImageClosed.lean#L45-L48

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_SummandReduction
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_ImageClosed
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}

theorem PretorsionImageClosed.LinearQuiver.prop_interval_of_prop_suffix (C : Subcategory (Statement.LinRep k n)) {a c b : Fin n}
    (hac : a ≤ c) (h : C.prop (suffix (k := k) a b c hac : Statement.LinRep k n)) :
    C.prop (interval k c b) := by sorry
