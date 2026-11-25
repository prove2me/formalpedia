-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_lt_glueRow_iff
-- name    : PretorsionImageClosed.LinearQuiver.lt_glueRow_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:45:12.803928+00:00
-- url     : https://prove2.me/theorems/d7220bd6-940c-4197-929d-57b53d9d13d6
-- title:
--   Linear Quiver: lt glue Row iff
-- statement:
--   The Linear Quiver construction uses the lt glue Row iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L162-L169
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L162-L169

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

theorem PretorsionImageClosed.LinearQuiver.lt_glueRow_iff {p : CutoffPair n} {Cont : Finset (Fin (n + 1))} {a : Fin (n + 1)} :
    n < (glueRow p Cont).β a ↔ a ∈ Cont := by sorry
