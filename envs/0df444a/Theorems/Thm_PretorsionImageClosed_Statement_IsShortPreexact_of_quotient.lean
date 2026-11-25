-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_IsShortPreexact_of_quotient
-- name    : PretorsionImageClosed.Statement.IsShortPreexact.of_quotient
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:56:40.931809+00:00
-- url     : https://prove2.me/theorems/4ea70a38-2b38-482a-b68e-c4bc0f1db0b8
-- title:
--   Is Short Preexact: of quotient
-- statement:
--   The Is Short Preexact construction uses the of quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Lifting.lean#L31-L69
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Lifting.lean#L31-L69

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lifting
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits
variable {C : Type*} [Category C] [Abelian C] {Z : ObjectProperty C}

theorem PretorsionImageClosed.Statement.IsShortPreexact.of_quotient {X V A B F : C} (π : X ⟶ V) [Epi π] (ι : A ⟶ X) [Mono ι]
    (πA : A ⟶ B) [Epi πA] (uV : B ⟶ V) [Mono uV] (vV : V ⟶ F) (hs : IsShortPreexact Z uV vV)
    (hcomm : πA ≫ uV = ι ≫ π)
    (hpull : ∀ {Y : C} (u' : Y ⟶ X) (w : Y ⟶ B), w ≫ uV = u' ≫ π → ∃ w' : Y ⟶ A, w' ≫ ι = u')
    (hK : ∀ {W : C} (g : A ⟶ W), Z W → kernel.ι πA ≫ g = 0) :
    IsShortPreexact Z ι (π ≫ vV) := by sorry
