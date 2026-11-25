-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_colOf_glue
-- name    : PretorsionImageClosed.LinearQuiver.colOf_glue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:45:15.663782+00:00
-- url     : https://prove2.me/theorems/39d0262b-8be4-5d64-baca-cfbade3dfa12
-- title:
--   Linear Quiver: col Of glue
-- statement:
--   The Linear Quiver construction uses the col Of glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L333-L343
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L333-L343

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

theorem PretorsionImageClosed.LinearQuiver.colOf_glue (p : CutoffPair n) (Cont : Finset (Fin (n + 1))) (c : Option (Fin (n + 1)))
    (hc : Allowed p Cont c) : colOf (glue p Cont c hc) = c := by sorry
