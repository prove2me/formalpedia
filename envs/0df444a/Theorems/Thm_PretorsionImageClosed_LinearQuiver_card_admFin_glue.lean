-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_card_admFin_glue
-- name    : PretorsionImageClosed.LinearQuiver.card_admFin_glue
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:20:36.769011+00:00
-- url     : https://prove2.me/theorems/c11b9829-f679-555f-95ea-dad67ae4853e
-- title:
--   Linear Quiver: card adm Fin glue
-- statement:
--   The Linear Quiver construction uses the card adm Fin glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/FamilyRestriction.lean#L330-L350
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/FamilyRestriction.lean#L330-L350

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

theorem PretorsionImageClosed.LinearQuiver.card_admFin_glue {D : IntervalFamily n} {J : Finset (Fin (n + 1))} (hJ : J ⊆ adm D) :
    (admFin (D.glue J)).card + (if J = ∅ then 0 else 1) =
      J.card + ((adm D).filter (fun c => ∀ a ∈ J, c ≤ a)).card := by sorry
