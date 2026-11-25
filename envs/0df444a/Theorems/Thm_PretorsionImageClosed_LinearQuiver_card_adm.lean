-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_card_adm
-- name    : PretorsionImageClosed.LinearQuiver.card_adm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:08:05.562323+00:00
-- url     : https://prove2.me/theorems/9397dce3-f40c-5379-ba7e-3c328d95e6e2
-- title:
--   Linear Quiver: card adm
-- statement:
--   The Linear Quiver construction uses the card adm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/FamilyRestriction.lean#L87-L91
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/FamilyRestriction.lean#L87-L91

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

theorem PretorsionImageClosed.LinearQuiver.card_adm (D : IntervalFamily n) : (adm D).card = (admFin D).card + 1 := by sorry
