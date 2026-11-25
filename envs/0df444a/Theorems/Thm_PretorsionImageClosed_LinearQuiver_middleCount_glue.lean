-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_middleCount_glue
-- name    : PretorsionImageClosed.LinearQuiver.middleCount_glue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:46:26.876262+00:00
-- url     : https://prove2.me/theorems/b781d3e0-84a5-4c17-b979-11cf4f0eac1c
-- title:
--   Linear Quiver: middle Count glue
-- statement:
--   The Linear Quiver construction uses the middle Count glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L399-L406
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L399-L406

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

theorem PretorsionImageClosed.LinearQuiver.middleCount_glue (p : CutoffPair n) (Cont : Finset (Fin (n + 1))) (c : Option (Fin (n + 1)))
    (hC : Cont ⊆ candRows p) :
    middleCount (glueRow p Cont) (glueCol p c) =
      middleCount p.1.1 p.1.2 + (Cont.filter (fun a => colValue c ≤ a.val)).card := by sorry
