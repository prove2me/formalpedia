-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_isLeast_leastRealization
-- name    : PretorsionImageClosed.Statement.isLeast_leastRealization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:53:21.753982+00:00
-- url     : https://prove2.me/theorems/1899937b-b140-4f87-92c6-29550598e637
-- title:
--   Statement: is Least least Realization
-- statement:
--   **Corollary 4.7**: the least realization is the least element of `PT_Z`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Realizations/LeastRealization.lean#L80-L82
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Realizations/LeastRealization.lean#L80-L82

module
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA
public import Definitions.Def_PretorsionImageClosed_Pretorsion_FixedMiddle
public import Definitions.Def_PretorsionImageClosed_Realizations_LeastRealization
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C]
variable (Z : Subcategory C) (hZ : Z.IsImageClosed)
variable {Z}

theorem PretorsionImageClosed.Statement.isLeast_leastRealization :
    IsLeast {P : PretorsionTheory C | P.middle = Z.prop} (leastRealization Z hZ) := by sorry
