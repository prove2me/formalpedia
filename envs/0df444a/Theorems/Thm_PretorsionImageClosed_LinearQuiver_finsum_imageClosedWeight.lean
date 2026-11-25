-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_finsum_imageClosedWeight
-- name    : PretorsionImageClosed.LinearQuiver.finsum_imageClosedWeight
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:05:01.177403+00:00
-- url     : https://prove2.me/theorems/507db198-76b2-5e5e-afb4-3ca44fc7844c
-- title:
--   Linear Quiver: finsum image Closed Weight
-- statement:
--   The Linear Quiver construction uses the finsum image Closed Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/IntervalFamilies.lean#L187-L190
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/IntervalFamilies.lean#L187-L190

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

theorem PretorsionImageClosed.LinearQuiver.finsum_imageClosedWeight :
    ∑ᶠ Z : ImageClosedSubcategory k n, imageClosedWeight k n Z = ∑ D : ClosedFamily n, fWeight D := by sorry
