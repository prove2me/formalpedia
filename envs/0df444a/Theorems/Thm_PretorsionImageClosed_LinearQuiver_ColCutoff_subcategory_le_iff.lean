-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_ColCutoff_subcategory_le_iff
-- name    : PretorsionImageClosed.LinearQuiver.ColCutoff.subcategory_le_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:05:31.255449+00:00
-- url     : https://prove2.me/theorems/5b557b2f-3070-4578-992b-96120d700f34
-- title:
--   Col Cutoff: subcategory le iff
-- statement:
--   **Proposition 6.1**, the order: `F_α ⊇ F_α'` iff `α ≤ α'`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Cutoffs.lean#L253-L267
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Cutoffs.lean#L253-L267

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

theorem PretorsionImageClosed.LinearQuiver.ColCutoff.subcategory_le_iff (α α' : ColCutoff n) :
    α'.subcategory (k := k) ≤ α.subcategory ↔ ∀ d, α.α d ≤ α'.α d := by sorry
