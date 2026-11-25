-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_finInf_prop_iff
-- name    : PretorsionImageClosed.Statement.finInf_prop_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:30:55.028232+00:00
-- url     : https://prove2.me/theorems/b00679ed-40b4-446e-a184-709aae434cdc
-- title:
--   Statement: fin Inf prop iff
-- statement:
--   The Statement construction uses the fin Inf prop iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Partners.lean#L173-L175
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Partners.lean#L173-L175

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
variable {ι : Type*} (F : ι → Subcategory C)

theorem PretorsionImageClosed.Statement.finInf_prop_iff (J : Finset ι) (X : C) : (finInf F J).prop X ↔ ∀ i ∈ J, (F i).prop X := by sorry
