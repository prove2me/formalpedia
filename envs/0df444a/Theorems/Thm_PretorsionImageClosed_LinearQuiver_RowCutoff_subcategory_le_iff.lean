-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_RowCutoff_subcategory_le_iff
-- name    : PretorsionImageClosed.LinearQuiver.RowCutoff.subcategory_le_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:03:34.937383+00:00
-- url     : https://prove2.me/theorems/db9f14ea-64ff-458c-9b8d-686d50bd86f7
-- title:
--   Row Cutoff: subcategory le iff
-- statement:
--   **Proposition 6.1**, the order: `T_β ⊆ T_β'` iff `β ≤ β'`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Cutoffs.lean#L237-L250
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Cutoffs.lean#L237-L250

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalSets
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Cutoffs
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
attribute [local instance] Classical.propDecidable

theorem PretorsionImageClosed.LinearQuiver.RowCutoff.subcategory_le_iff (β β' : RowCutoff n) :
    β.subcategory (k := k) ≤ β'.subcategory ↔ ∀ a, β.β a ≤ β'.β a := by sorry
