-- Prove2me | Theorems.Thm_P2M_PretorsionImageClosed_Subobject_kernelSubobject_arrow_comp_cokernel___push_f45f7adb5033
-- name    : P2M_PretorsionImageClosed_Subobject_kernelSubobject_arrow_comp_cokernel___push_f45f7adb5033
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:48:29.329802+00:00
-- url     : https://prove2.me/theorems/343b15c1-985f-5a03-80b9-8c5e13c9912c
-- title:
--   P2 M Pretorsion Image Closed Subobject kernel Subobject arrow comp cokernel   push f45f7adb5033: P2 M Pretorsion Image Closed Subobject kernel Subobject arrow comp cokernel   push f45f7adb5033
-- statement:
--   The kernel of `S → X → X/(push S K)` is `K`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Preimage.lean#L237-L251
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Subobjects/Preimage.lean#L237-L251

module
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
variable {C : Type*} [Category C] [Abelian C]
variable {C : Type*} [Category C] [Abelian C] {X : C} (S : Subobject X) (K : Subobject (S : C))

theorem P2M_PretorsionImageClosed_Subobject_kernelSubobject_arrow_comp_cokernel___push_f45f7adb5033 :
    kernelSubobject (S.arrow ≫ cokernel.π (Subobject.push S K).arrow) = K := by sorry

alias «PretorsionImageClosed».«Subobject».«kernelSubobject_arrow_comp_cokernel_π_push» := P2M_PretorsionImageClosed_Subobject_kernelSubobject_arrow_comp_cokernel___push_f45f7adb5033
