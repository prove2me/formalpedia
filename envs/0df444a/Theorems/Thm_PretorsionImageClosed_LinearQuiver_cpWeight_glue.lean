-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_cpWeight_glue
-- name    : PretorsionImageClosed.LinearQuiver.cpWeight_glue
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T06:46:12.674172+00:00
-- url     : https://prove2.me/theorems/7a29df65-e4ad-5f1c-a122-b4357aca9254
-- title:
--   Linear Quiver: cp Weight glue
-- statement:
--   The Linear Quiver construction uses the cp Weight glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L408-L414
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L408-L414

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

theorem PretorsionImageClosed.LinearQuiver.cpWeight_glue (p : CutoffPair n) (Cont : Finset (Fin (n + 1))) (c : Option (Fin (n + 1)))
    (hC : Cont ⊆ candRows p) (hc : Allowed p Cont c) :
    cpWeight (glue p Cont c hc) = C (q ^ middleCount p.1.1 p.1.2) *
      (X ^ Cont.card * C (q ^ (Cont.filter (fun a => colValue c ≤ a.val)).card)) := by sorry
