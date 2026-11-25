-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_IntervalFamily_glue_JOf
-- name    : PretorsionImageClosed.LinearQuiver.IntervalFamily.glue_JOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:09:11.36384+00:00
-- url     : https://prove2.me/theorems/d707af47-79f3-4a26-9b45-0eb1399263f9
-- title:
--   Interval Family: glue JOf
-- statement:
--   Construction 8.3: every family on `n + 1` vertices is the extension of its restriction.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/FamilyRestriction.lean#L151-L169
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/FamilyRestriction.lean#L151-L169

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalFamilies
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_FamilyRestriction
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open Statement Polynomial Finset
open PretorsionImageClosed.LinearQuiver
variable {n : ℕ}

theorem PretorsionImageClosed.LinearQuiver.IntervalFamily.glue_JOf (D : IntervalFamily (n + 1)) : D.restrict.glue (JOf D) = D := by sorry
