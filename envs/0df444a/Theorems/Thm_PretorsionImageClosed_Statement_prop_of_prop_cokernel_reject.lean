-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_prop_of_prop_cokernel_reject
-- name    : PretorsionImageClosed.Statement.prop_of_prop_cokernel_reject
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:59:13.432357+00:00
-- url     : https://prove2.me/theorems/57151a93-876c-40ed-a570-c50c880e0a1b
-- title:
--   Statement: prop of prop cokernel reject
-- statement:
--   **Lemma 3.4.** Let `(T, F)` be a pretorsion theory and `G ⊇ F` subobject-closed. If
--   `X / r_G(X) ∈ T`, then `X ∈ T`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Partners.lean#L278-L292
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Partners.lean#L278-L292

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

theorem PretorsionImageClosed.Statement.prop_of_prop_cokernel_reject {T F G : Subcategory C} (hP : IsPretorsionTheory T.prop F.prop)
    (hG : G.IsSubobjectClosed) (hFG : ∀ Y, F.prop Y → G.prop Y) {X : C}
    (hX : T.prop (cokernel (G.reject X).arrow)) : T.prop X := by sorry
