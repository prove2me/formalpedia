-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_card_glue
-- name    : PretorsionImageClosed.LinearQuiver.card_glue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:09:13.783038+00:00
-- url     : https://prove2.me/theorems/020d6475-f3c0-4ecd-9b9b-d5a159f84baf
-- title:
--   Linear Quiver: card glue
-- statement:
--   The Linear Quiver construction uses the card glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/FamilyRestriction.lean#L252-L274
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/FamilyRestriction.lean#L252-L274

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

theorem PretorsionImageClosed.LinearQuiver.card_glue (D : IntervalFamily n) (J : Finset (Fin (n + 1))) :
    (D.glue J).D.card = D.D.card + J.card := by sorry
