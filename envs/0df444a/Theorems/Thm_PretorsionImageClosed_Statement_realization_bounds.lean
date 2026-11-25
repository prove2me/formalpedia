-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_realization_bounds
-- name    : PretorsionImageClosed.Statement.realization_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:41:45.083862+00:00
-- url     : https://prove2.me/theorems/6cd630f2-82fc-43e6-a809-79796a024fa9
-- title:
--   Statement: realization bounds
-- statement:
--   **Corollary 4.7.** Every pretorsion theory with intersection `Z` lies between the least
--   and the greatest realization of `Z`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Realizations/LeastRealization.lean#L69-L77
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Realizations/LeastRealization.lean#L69-L77

module
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA
public import Definitions.Def_PretorsionImageClosed_Pretorsion_FixedMiddle
public import Definitions.Def_PretorsionImageClosed_Realizations_LeastRealization
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C]
variable (Z : Subcategory C) (hZ : Z.IsImageClosed)
variable {Z}

theorem PretorsionImageClosed.Statement.realization_bounds (P : PretorsionTheory C) (hP : P.middle = Z.prop) :
    leastRealization Z hZ ≤ P ∧ P ≤ greatestRealization Z hZ := by sorry
