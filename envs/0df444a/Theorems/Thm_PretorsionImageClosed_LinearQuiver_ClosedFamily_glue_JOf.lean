-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_ClosedFamily_glue_JOf
-- name    : PretorsionImageClosed.LinearQuiver.ClosedFamily.glue_JOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:16:09.455803+00:00
-- url     : https://prove2.me/theorems/d59814e1-309a-4f9e-96e7-8e6626d27c61
-- title:
--   Closed Family: glue JOf
-- statement:
--   The Closed Family construction uses the glue JOf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/FamilyRestriction.lean#L246-L248
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/FamilyRestriction.lean#L246-L248

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

theorem PretorsionImageClosed.LinearQuiver.ClosedFamily.glue_JOf (D : ClosedFamily (n + 1)) :
    D.restrict.glue (JOf D.1) (JOf_subset_adm D.2) = D := by sorry
