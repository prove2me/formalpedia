-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_isGreatest_greatestRealization
-- name    : PretorsionImageClosed.Statement.isGreatest_greatestRealization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:53:17.731709+00:00
-- url     : https://prove2.me/theorems/ec2396d6-a580-55c7-ae3e-952a6e506ae6
-- title:
--   Statement: is Greatest greatest Realization
-- statement:
--   Corollary 4.5 in the form used by Corollary 4.7: the greatest realization is the greatest
--   element of `PT_Z`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Realizations/LeastRealization.lean#L86-L88
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Realizations/LeastRealization.lean#L86-L88

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

theorem PretorsionImageClosed.Statement.isGreatest_greatestRealization :
    IsGreatest {P : PretorsionTheory C | P.middle = Z.prop} (greatestRealization Z hZ) := by sorry
