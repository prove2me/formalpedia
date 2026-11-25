-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_card_adm_glue
-- name    : PretorsionImageClosed.LinearQuiver.card_adm_glue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:21:42.62918+00:00
-- url     : https://prove2.me/theorems/064a59d2-c99d-4328-9cef-84dd8c524b78
-- title:
--   Linear Quiver: card adm glue
-- statement:
--   Lemma 8.4(2): the number of admissible starts of `D_J` is `admCount (adm D) J`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/FamilyRestriction.lean#L353-L365
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/FamilyRestriction.lean#L353-L365

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

theorem PretorsionImageClosed.LinearQuiver.card_adm_glue {D : IntervalFamily n} {J : Finset (Fin (n + 1))} (hJ : J ⊆ adm D) :
    (adm (D.glue J)).card = admCount (adm D) J := by sorry
