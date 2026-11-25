-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_indCard_inf
-- name    : PretorsionImageClosed.LinearQuiver.indCard_inf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:18:38.648547+00:00
-- url     : https://prove2.me/theorems/29b0237a-ddfb-4e62-8171-7602f84bccb6
-- title:
--   Linear Quiver: ind Card inf
-- statement:
--   The Linear Quiver construction uses the ind Card inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffWeights.lean#L64-L81
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffWeights.lean#L64-L81

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffCriterion
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Counting
public import Definitions.Def_PretorsionImageClosed_Gandhi_Delta
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffWeights
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement Polynomial Finset
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}

theorem PretorsionImageClosed.LinearQuiver.indCard_inf (β : RowCutoff n) (α : ColCutoff n) :
    indCard ((β.subcategory (k := k)).prop ⊓ α.subcategory.prop) = middleCount β α := by sorry
