-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_intersectionClosed_of_isImageClosed
-- name    : PretorsionImageClosed.LinearQuiver.intersectionClosed_of_isImageClosed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:11:35.595471+00:00
-- url     : https://prove2.me/theorems/cd76b2e4-33f1-4af2-beaa-293e7040b37d
-- title:
--   Linear Quiver: intersection Closed of is Image Closed
-- statement:
--   Theorem 5.5, (⇒).
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/ImageClosed.lean#L51-L66
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/ImageClosed.lean#L51-L66

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

theorem PretorsionImageClosed.LinearQuiver.intersectionClosed_of_isImageClosed (C : Subcategory (Statement.LinRep k n))
    (hC : C.IsImageClosed) : IntersectionClosed C := by sorry
