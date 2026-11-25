-- Prove2me | Theorems.Thm_PretorsionImageClosed_Statement_IsPrekernel_mono
-- name    : PretorsionImageClosed.Statement.IsPrekernel.mono
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:48:27.043341+00:00
-- url     : https://prove2.me/theorems/456c7058-6fc8-464f-a289-038ac0517ffd
-- title:
--   Is Prekernel: mono
-- statement:
--   Lemma 2.11: a `Z`-prekernel is a monomorphism.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Basic.lean#L33-L39
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Basic.lean#L33-L39

module
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
public import Theorems.Thm_PretorsionImageClosed_Statement_IsTrivial_mono

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits ZeroObject
open PretorsionImageClosed.Statement
variable {C : Type*} [Category C] {Z : ObjectProperty C}

theorem PretorsionImageClosed.Statement.IsPrekernel.mono {T X F : C} {u : T ⟶ X} {v : X ⟶ F} (h : IsPrekernel Z u v) : Mono u := by sorry
