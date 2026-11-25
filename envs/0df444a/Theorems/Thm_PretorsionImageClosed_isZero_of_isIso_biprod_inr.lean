-- Prove2me | Theorems.Thm_PretorsionImageClosed_isZero_of_isIso_biprod_inr
-- name    : PretorsionImageClosed.isZero_of_isIso_biprod_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:00:58.63396+00:00
-- url     : https://prove2.me/theorems/83ecb1ce-568a-543d-961e-7ddd17ce7290
-- title:
--   Pretorsion Image Closed: is Zero of is Iso biprod inr
-- statement:
--   If `biprod.inr : N ⟶ M ⊞ N` is an isomorphism then `M` is zero.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Biproducts/Basic.lean#L27-L32
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Biproducts/Basic.lean#L27-L32

module
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Definitions.Def_PretorsionImageClosed_Biproducts_Basic
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits

theorem PretorsionImageClosed.isZero_of_isIso_biprod_inr {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {M N : C} (h : IsIso (biprod.inr : N ⟶ M ⊞ N)) : IsZero M := by sorry
