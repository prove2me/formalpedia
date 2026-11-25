-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_traceRejectCondition_of_quotient_reject
-- name    : PretorsionImageClosed.Statement.traceRejectCondition_of_quotient_reject
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:38:35.86179+00:00
-- url     : https://prove2.me/theorems/a5ac6619-96be-4fcf-995c-7a488c9711d3
-- title:
--   Statement: trace Reject Condition of quotient reject
-- statement:
--   The inductive step of Proposition 3.2: if `(T, F)` satisfies (2.4) at `X`, `G ⊆ F` is
--   subobject-closed and `(T, G)` satisfies (2.4) at `X / r_F(X)`, then `(T, G)` satisfies (2.4)
--   at `X`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Partners.lean#L72-L120
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Partners.lean#L72-L120

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

theorem PretorsionImageClosed.Statement.traceRejectCondition_of_quotient_reject {T F G : Subcategory C} (hT : T.IsQuotientClosed)
    (hF : F.IsSubobjectClosed) (hG : G.IsSubobjectClosed) (hGF : ∀ Y, G.prop Y → F.prop Y) {X : C}
    (hX : TraceRejectCondition T F X) (hV : TraceRejectCondition T G (cokernel (F.reject X).arrow)) :
    TraceRejectCondition T G X := by sorry
