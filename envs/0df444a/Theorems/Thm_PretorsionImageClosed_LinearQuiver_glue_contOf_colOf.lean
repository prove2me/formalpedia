-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_glue_contOf_colOf
-- name    : PretorsionImageClosed.LinearQuiver.glue_contOf_colOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:45:06.828798+00:00
-- url     : https://prove2.me/theorems/69b3c285-1a30-4c90-8eef-1b4a0b19ea16
-- title:
--   Linear Quiver: glue cont Of col Of
-- statement:
--   The Linear Quiver construction uses the glue cont Of col Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L307-L325
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L307-L325

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

theorem PretorsionImageClosed.LinearQuiver.glue_contOf_colOf (x : CutoffPair (n + 1)) :
    glue x.restrict (contOf x) (colOf x) (allowed_colOf x) = x := by sorry
