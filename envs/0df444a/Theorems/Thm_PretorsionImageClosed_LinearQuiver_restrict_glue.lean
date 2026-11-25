-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_restrict_glue
-- name    : PretorsionImageClosed.LinearQuiver.restrict_glue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:46:03.333859+00:00
-- url     : https://prove2.me/theorems/89c1386b-4fd2-4223-9920-35ca10758319
-- title:
--   Linear Quiver: restrict glue
-- statement:
--   The Linear Quiver construction uses the restrict glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L229-L245
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L229-L245

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

theorem PretorsionImageClosed.LinearQuiver.restrict_glue (p : CutoffPair n) (Cont : Finset (Fin (n + 1))) (c : Option (Fin (n + 1)))
    (hC : Cont ⊆ candRows p) (hc : Allowed p Cont c) : (glue p Cont c hc).restrict = p := by sorry
