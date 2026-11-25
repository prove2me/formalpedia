-- Prove2me | Theorems.Thm_PretorsionImageClosed_FGModuleCat_hom_hom_sum
-- name    : PretorsionImageClosed.FGModuleCat.hom_hom_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:14:53.691557+00:00
-- url     : https://prove2.me/theorems/43e7c1c2-80dd-466d-a69b-374aeece972d
-- title:
--   FGModule Cat: hom hom sum
-- statement:
--   The underlying linear map of a finite sum of morphisms.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/FiniteModules.lean#L75-L79
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/FiniteModules.lean#L75-L79

module
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.FGModuleCat.Limits
public import Mathlib.Algebra.Category.FGModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Definitions.Def_PretorsionImageClosed_Modules_FiniteModules
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
open PretorsionImageClosed.FGModuleCat
variable {R : Type*} [Ring R] [IsNoetherianRing R]
omit [IsNoetherianRing R]

theorem PretorsionImageClosed.FGModuleCat.hom_hom_sum {J : Type*} [Fintype J] {X Y : FGModuleCat R} (f : J → (X ⟶ Y)) :
    (∑ j, f j).hom.hom = ∑ j, (f j).hom.hom := by sorry
