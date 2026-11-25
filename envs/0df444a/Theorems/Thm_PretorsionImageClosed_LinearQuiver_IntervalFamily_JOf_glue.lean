-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_IntervalFamily_JOf_glue
-- name    : PretorsionImageClosed.LinearQuiver.IntervalFamily.JOf_glue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:14:11.928896+00:00
-- url     : https://prove2.me/theorems/5e0a1c8e-8543-4ccc-a80a-e9bbb2ab98ca
-- title:
--   Interval Family: JOf glue
-- statement:
--   The Interval Family construction uses the JOf glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/FamilyRestriction.lean#L171-L173
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/FamilyRestriction.lean#L171-L173

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

theorem PretorsionImageClosed.LinearQuiver.IntervalFamily.JOf_glue (D : IntervalFamily n) (J : Finset (Fin (n + 1))) : JOf (D.glue J) = J := by sorry
