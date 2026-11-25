-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_isImageClosed_of_intersectionClosed
-- name    : PretorsionImageClosed.LinearQuiver.isImageClosed_of_intersectionClosed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:11:18.486827+00:00
-- url     : https://prove2.me/theorems/f59e0e54-4975-43d1-8913-cfde98f8e687
-- title:
--   Linear Quiver: is Image Closed of intersection Closed
-- statement:
--   Theorem 5.5, (⇐).
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/ImageClosed.lean#L120-L143
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/ImageClosed.lean#L120-L143

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

theorem PretorsionImageClosed.LinearQuiver.isImageClosed_of_intersectionClosed (C : Subcategory (Statement.LinRep k n))
    (hC : IntersectionClosed C) : C.IsImageClosed := by sorry
