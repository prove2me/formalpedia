-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_TraceRejectCondition_of_reject_eq
-- name    : PretorsionImageClosed.Statement.TraceRejectCondition.of_reject_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:40:03.205279+00:00
-- url     : https://prove2.me/theorems/57ce75f7-837f-4dc6-8d7e-4e0035f36361
-- title:
--   Trace Reject Condition: of reject eq
-- statement:
--   Changing the second component without changing the rejects of `X` and `t(X)` preserves the
--   trace–reject condition at `X`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Partners.lean#L149-L164
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Partners.lean#L149-L164

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

theorem PretorsionImageClosed.Statement.TraceRejectCondition.of_reject_eq {T F G : Subcategory C} {X : C}
    (h : TraceRejectCondition T F X) (h1 : G.reject X = F.reject X)
    (h2 : G.reject (T.trace X : C) = F.reject (T.trace X : C)) : TraceRejectCondition T G X := by sorry
