-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_traceRejectCondition_of_prop
-- name    : PretorsionImageClosed.Statement.traceRejectCondition_of_prop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:28:55.973769+00:00
-- url     : https://prove2.me/theorems/057eebf2-dc7b-5d3d-8fcd-909f3ddf9ea1
-- title:
--   Statement: trace Reject Condition of prop
-- statement:
--   The trace–reject condition at an object of `F`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Criterion.lean#L52-L68
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Criterion.lean#L52-L68

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_TraceReject
public import Definitions.Def_PretorsionImageClosed_Subobjects_Quotients
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Criterion
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C] {T F : Subcategory C} {X : C}

theorem PretorsionImageClosed.Statement.traceRejectCondition_of_prop (hT : T.IsQuotientClosed) (hF : F.IsSubobjectClosed)
    (hX : F.prop X) : TraceRejectCondition T F X := by sorry
