-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_imageClosedWeight_eq
-- name    : PretorsionImageClosed.LinearQuiver.imageClosedWeight_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:04:59.735509+00:00
-- url     : https://prove2.me/theorems/507c0df0-c428-5588-8b19-19ab68451a77
-- title:
--   Linear Quiver: image Closed Weight eq
-- statement:
--   The Linear Quiver construction uses the image Closed Weight eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/IntervalFamilies.lean#L168-L173
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/IntervalFamilies.lean#L168-L173

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_ImageClosed
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Counting
public import Definitions.Def_PretorsionImageClosed_Gandhi_Delta
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalFamilies
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement Polynomial Finset
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}

theorem PretorsionImageClosed.LinearQuiver.imageClosedWeight_eq (Z : ImageClosedSubcategory k n) :
    imageClosedWeight k n Z = fWeight (imageClosedEquiv Z) := by sorry
