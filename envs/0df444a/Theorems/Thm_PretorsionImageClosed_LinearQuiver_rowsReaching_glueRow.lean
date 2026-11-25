-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_rowsReaching_glueRow
-- name    : PretorsionImageClosed.LinearQuiver.rowsReaching_glueRow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:45:44.937307+00:00
-- url     : https://prove2.me/theorems/c5c0c53e-85ca-5f60-bad0-c93c4eb4a829
-- title:
--   Linear Quiver: rows Reaching glue Row
-- statement:
--   The Linear Quiver construction uses the rows Reaching glue Row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L347-L352
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L347-L352

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

theorem PretorsionImageClosed.LinearQuiver.rowsReaching_glueRow (p : CutoffPair n) (Cont : Finset (Fin (n + 1))) :
    (glueRow p Cont).rowsReaching = Cont.card := by sorry
