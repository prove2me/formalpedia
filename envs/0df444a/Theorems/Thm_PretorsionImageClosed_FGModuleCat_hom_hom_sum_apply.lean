-- Prove2me | Theorems.Thm_PretorsionImageClosed_FGModuleCat_hom_hom_sum_apply
-- name    : PretorsionImageClosed.FGModuleCat.hom_hom_sum_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:52:50.345834+00:00
-- url     : https://prove2.me/theorems/2848e159-33fa-4e1b-825c-6d5d14ed9aa1
-- title:
--   FGModule Cat: hom hom sum apply
-- statement:
--   The FGModule Cat construction uses the hom hom sum apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/FiniteModules.lean#L82-L84
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/FiniteModules.lean#L82-L84

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

theorem PretorsionImageClosed.FGModuleCat.hom_hom_sum_apply {J : Type*} [Fintype J] {X Y : FGModuleCat R} (f : J → (X ⟶ Y))
    (x : X) : (∑ j, f j).hom.hom x = ∑ j, (f j).hom.hom x := by sorry
