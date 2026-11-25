-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_isPretorsionTheory_of_reject_trace
-- name    : PretorsionImageClosed.Statement.isPretorsionTheory_of_reject_trace
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:59:14.681832+00:00
-- url     : https://prove2.me/theorems/c8b31476-b01c-48df-9577-983082b0d6da
-- title:
--   Statement: is Pretorsion Theory of reject trace
-- statement:
--   **Lemma 3.3.** If `r(X) = r(t(X))` for every `X` and `T = {X : X/r(X) ∈ T ∩ F}`, then
--   `(T, F)` is a pretorsion theory.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Partners.lean#L258-L274
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Partners.lean#L258-L274

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

theorem PretorsionImageClosed.Statement.isPretorsionTheory_of_reject_trace {T F : Subcategory C} (hT : T.IsQuotientClosed)
    (hF : F.IsSubobjectClosed)
    (hrt : ∀ X : C, ∃ h : F.reject X ≤ T.trace X,
      F.reject (T.trace X : C) = Subobject.mk (Subobject.ofLE _ _ h))
    (hTZ : ∀ X : C, T.prop X ↔ (T.prop ⊓ F.prop) (cokernel (F.reject X).arrow)) :
    IsPretorsionTheory T.prop F.prop := by sorry
