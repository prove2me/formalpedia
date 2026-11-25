-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_card_candRows
-- name    : PretorsionImageClosed.LinearQuiver.card_candRows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:44:47.511066+00:00
-- url     : https://prove2.me/theorems/fd94306a-4c86-4e34-8306-2ae7062083a2
-- title:
--   Linear Quiver: card cand Rows
-- statement:
--   The Linear Quiver construction uses the card cand Rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L104-L107
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L104-L107

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffWeights
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffRestriction
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open Statement Polynomial Finset
open PretorsionImageClosed.LinearQuiver
variable {n : ℕ}

theorem PretorsionImageClosed.LinearQuiver.card_candRows (p : CutoffPair n) : (candRows p).card = p.1.1.rowsReaching + 1 := by sorry
