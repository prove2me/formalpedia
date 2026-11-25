-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_length_cokernel_lt
-- name    : PretorsionImageClosed.Statement.length_cokernel_lt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:36:21.957798+00:00
-- url     : https://prove2.me/theorems/bcfbe320-2f37-5344-a70c-4813c61dd8db
-- title:
--   Statement: length cokernel lt
-- statement:
--   A nonzero subobject has a strictly shorter quotient.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Partners.lean#L61-L67
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Partners.lean#L61-L67

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lifting
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Criterion
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Realization
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Partners
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C]

theorem PretorsionImageClosed.Statement.length_cokernel_lt {X : C} {S : Subobject X} (hS : S ≠ ⊥) :
    length (cokernel S.arrow) < length X := by sorry
