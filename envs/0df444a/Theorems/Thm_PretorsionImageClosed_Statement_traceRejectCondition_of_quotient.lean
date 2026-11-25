-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_traceRejectCondition_of_quotient
-- name    : PretorsionImageClosed.Statement.traceRejectCondition_of_quotient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:36:41.941294+00:00
-- url     : https://prove2.me/theorems/1c2069b4-bb83-4980-8d31-61d690f25453
-- title:
--   Statement: trace Reject Condition of quotient
-- statement:
--   The trace–reject condition from a presentation of the quotient `X / r(X)` by an
--   epimorphism `π : X ⟶ Q`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Criterion.lean#L92-L104
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Criterion.lean#L92-L104

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

theorem PretorsionImageClosed.Statement.traceRejectCondition_of_quotient (hT : T.IsQuotientClosed) {Q : C} (π : X ⟶ Q) [Epi π]
    (hker : kernelSubobject π = F.reject X) (h1 : F.reject X ≤ T.trace X)
    (h2 : F.reject (T.trace X : C) = Subobject.mk (Subobject.ofLE _ _ h1))
    (h3 : T.trace Q = imageSubobject ((T.trace X).arrow ≫ π)) : TraceRejectCondition T F X := by sorry
