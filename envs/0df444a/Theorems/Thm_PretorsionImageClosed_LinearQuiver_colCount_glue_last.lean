-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_colCount_glue_last
-- name    : PretorsionImageClosed.LinearQuiver.colCount_glue_last
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:46:59.843028+00:00
-- url     : https://prove2.me/theorems/3fa98923-6dbe-4c14-a5fe-a3b2b6fb963e
-- title:
--   Linear Quiver: col Count glue last
-- statement:
--   The Linear Quiver construction uses the col Count glue last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L390-L397
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L390-L397

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

theorem PretorsionImageClosed.LinearQuiver.colCount_glue_last (p : CutoffPair n) (Cont : Finset (Fin (n + 1))) (c : Option (Fin (n + 1))) :
    colCount (glueRow p Cont) (glueCol p c) (Fin.last n) =
      (Cont.filter (fun a => colValue c ≤ a.val)).card := by sorry
