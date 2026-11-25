-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_isPretorsionTheory_of_realization
-- name    : PretorsionImageClosed.Statement.isPretorsionTheory_of_realization
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:27:40.440957+00:00
-- url     : https://prove2.me/theorems/6e43282f-00e7-5682-a563-a99456dcbdbc
-- title:
--   Statement: is Pretorsion Theory of realization
-- statement:
--   **Lemma 3.7.**
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Realization.lean#L37-L136
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Realization.lean#L37-L136

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_TraceReject
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Realization
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits ZeroObject
open PretorsionImageClosed.Statement
open Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C] {T F : Subcategory C}

theorem PretorsionImageClosed.Statement.isPretorsionTheory_of_realization (hT : T.IsQuotientClosed) (hF : F.IsSubobjectClosed)
    (hF' : ∀ Y, F.prop Y ↔ (T.prop ⊓ F.prop) (T.trace Y : C))
    (hT' : ∀ E, T.prop E ↔ ∀ {Y : C} (f : E ⟶ Y), F.prop Y → IsTrivial (T.prop ⊓ F.prop) f) :
    IsPretorsionTheory T.prop F.prop := by sorry
