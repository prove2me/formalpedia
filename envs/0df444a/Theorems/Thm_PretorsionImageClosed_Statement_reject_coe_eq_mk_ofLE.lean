-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_reject_coe_eq_mk_ofLE
-- name    : PretorsionImageClosed.Statement.reject_coe_eq_mk_ofLE
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:35:16.359274+00:00
-- url     : https://prove2.me/theorems/a3345f76-e883-4828-955b-582818c975c0
-- title:
--   Statement: reject coe eq mk of LE
-- statement:
--   `r(t) = r` as subobjects of `t`, from representatives: `t = mk ι`, `r = mk (κ ≫ ι)` and
--   `r_F(A) = mk κ`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Criterion.lean#L37-L49
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Criterion.lean#L37-L49

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

theorem PretorsionImageClosed.Statement.reject_coe_eq_mk_ofLE (hF : F.IsSubobjectClosed) {t r : Subobject X} (h : r ≤ t)
    {A B : C} (ι : A ⟶ X) [Mono ι] (κ : B ⟶ A) [Mono κ] (ht : t = Subobject.mk ι)
    (hr : r = Subobject.mk (κ ≫ ι)) (hA : F.reject A = Subobject.mk κ) :
    F.reject (t : C) = Subobject.mk (Subobject.ofLE r t h) := by sorry
