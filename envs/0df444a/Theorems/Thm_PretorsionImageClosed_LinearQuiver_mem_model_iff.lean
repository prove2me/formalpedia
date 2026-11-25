-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_mem_model_iff
-- name    : PretorsionImageClosed.LinearQuiver.mem_model_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:47:03.493404+00:00
-- url     : https://prove2.me/theorems/28d7bbbd-e3b3-4bf0-a64e-0b38aa367f1d
-- title:
--   Linear Quiver: mem model iff
-- statement:
--   The Linear Quiver construction uses the mem model iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L432-L434
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L432-L434

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

theorem PretorsionImageClosed.LinearQuiver.mem_model_iff {p : CutoffPair n} {y : Σ _ : Finset (Fin (n + 1)), Option (Fin (n + 1))} :
    y ∈ model p ↔ y.1 ⊆ candRows p ∧ Allowed p y.1 y.2 := by sorry
