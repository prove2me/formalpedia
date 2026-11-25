-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_colCount_glue_castSucc
-- name    : PretorsionImageClosed.LinearQuiver.colCount_glue_castSucc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:45:46.9819+00:00
-- url     : https://prove2.me/theorems/86fcf2a5-753f-5a94-b2bc-c20c5d5c363b
-- title:
--   Linear Quiver: col Count glue cast Succ
-- statement:
--   The Linear Quiver construction uses the col Count glue cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L354-L388
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L354-L388

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

theorem PretorsionImageClosed.LinearQuiver.colCount_glue_castSucc (p : CutoffPair n) (Cont : Finset (Fin (n + 1)))
    (c : Option (Fin (n + 1))) (hC : Cont ⊆ candRows p) (d : Fin n) :
    colCount (glueRow p Cont) (glueCol p c) d.castSucc = colCount p.1.1 p.1.2 d := by sorry
