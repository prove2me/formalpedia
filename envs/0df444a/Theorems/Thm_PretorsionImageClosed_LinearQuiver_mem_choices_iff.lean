-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_mem_choices_iff
-- name    : PretorsionImageClosed.LinearQuiver.mem_choices_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T06:47:26.366724+00:00
-- url     : https://prove2.me/theorems/5b63c3d5-a6fd-4fcb-acbb-d0199b8ddeb2
-- title:
--   Linear Quiver: mem choices iff
-- statement:
--   The Linear Quiver construction uses the mem choices iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L422-L426
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L422-L426

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

theorem PretorsionImageClosed.LinearQuiver.mem_choices_iff {p : CutoffPair n} {Cont : Finset (Fin (n + 1))} {c : Option (Fin (n + 1))} :
    c ∈ choices p Cont ↔ Allowed p Cont c := by sorry
