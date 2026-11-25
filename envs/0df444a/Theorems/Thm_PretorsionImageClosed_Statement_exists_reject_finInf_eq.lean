-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_exists_reject_finInf_eq
-- name    : PretorsionImageClosed.Statement.exists_reject_finInf_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:43:39.720944+00:00
-- url     : https://prove2.me/theorems/7707b737-6b2b-5132-9371-99d3b42b3cc0
-- title:
--   Statement: exists reject fin Inf eq
-- statement:
--   The reject of the full intersection agrees with the reject of a finite subintersection.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Partners.lean#L211-L240
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Partners.lean#L211-L240

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lifting
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Criterion
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Realization
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Partners
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_IsImageClosed_iInf

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C]
variable {ι : Type*} (F : ι → Subcategory C)
variable {F} {T : Subcategory C} (hT : T.IsQuotientClosed) (h : ∀ i, IsPretorsionTheory T.prop (F i).prop)
include hT h
omit hT

theorem PretorsionImageClosed.Statement.exists_reject_finInf_eq (X : C) :
    ∃ J₀ : Finset ι, ∀ J : Finset ι, J₀ ⊆ J →
      (finInf F J).reject X = (Subcategory.iInf F).reject X := by sorry
