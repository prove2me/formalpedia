-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_IntervalFamily_restrict_glue
-- name    : PretorsionImageClosed.LinearQuiver.IntervalFamily.restrict_glue
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:08:45.912416+00:00
-- url     : https://prove2.me/theorems/8cf703d0-3daf-45ff-9d41-4cc1742ffde6
-- title:
--   Interval Family: restrict glue
-- statement:
--   The Interval Family construction uses the restrict glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/FamilyRestriction.lean#L139-L141
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/FamilyRestriction.lean#L139-L141

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

theorem PretorsionImageClosed.LinearQuiver.IntervalFamily.restrict_glue (D : IntervalFamily n) (J : Finset (Fin (n + 1))) : (D.glue J).restrict = D := by sorry
