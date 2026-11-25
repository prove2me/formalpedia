-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_traceRejectCondition_of_eq_top
-- name    : PretorsionImageClosed.Statement.traceRejectCondition_of_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:36:30.757832+00:00
-- url     : https://prove2.me/theorems/302111f5-276c-47ad-a808-83066570f8fe
-- title:
--   Statement: trace Reject Condition of eq top
-- statement:
--   The trace–reject condition when `r(X) = X = t(X)`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Criterion.lean#L71-L88
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Criterion.lean#L71-L88

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

theorem PretorsionImageClosed.Statement.traceRejectCondition_of_eq_top (hT : T.IsQuotientClosed) (hF : F.IsSubobjectClosed)
    (hr : F.reject X = ⊤) (ht : T.trace X = ⊤) : TraceRejectCondition T F X := by sorry
