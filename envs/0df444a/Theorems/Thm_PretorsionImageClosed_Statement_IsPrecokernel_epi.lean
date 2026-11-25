-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_IsPrecokernel_epi
-- name    : PretorsionImageClosed.Statement.IsPrecokernel.epi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:57:15.380891+00:00
-- url     : https://prove2.me/theorems/9274fa21-756c-473c-893c-d43021355851
-- title:
--   Is Precokernel: epi
-- statement:
--   Lemma 2.11: a `Z`-precokernel is an epimorphism.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Basic.lean#L42-L49
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Basic.lean#L42-L49

module
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits ZeroObject
open PretorsionImageClosed.Statement
variable {C : Type*} [Category C] {Z : ObjectProperty C}

theorem PretorsionImageClosed.Statement.IsPrecokernel.epi {T X F : C} {u : T ⟶ X} {v : X ⟶ F} (h : IsPrecokernel Z u v) :
    Epi v := by sorry
