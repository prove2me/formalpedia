-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_isImageClosed_iff_intersectionClosed
-- name    : PretorsionImageClosed.LinearQuiver.isImageClosed_iff_intersectionClosed
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:22:47.301407+00:00
-- url     : https://prove2.me/theorems/351abbd9-b720-5d8f-90d4-e69e661f7ea8
-- title:
--   Linear Quiver: is Image Closed iff intersection Closed
-- statement:
--   **Theorem 5.5.** A subcategory of `mod Λ_n` is image-closed iff its family of
--   support intervals is intersection-closed.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/ImageClosed.lean#L147-L149
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/ImageClosed.lean#L147-L149

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

theorem PretorsionImageClosed.LinearQuiver.isImageClosed_iff_intersectionClosed (C : Subcategory (Statement.LinRep k n)) :
    C.IsImageClosed ↔ IntersectionClosed C := by sorry
