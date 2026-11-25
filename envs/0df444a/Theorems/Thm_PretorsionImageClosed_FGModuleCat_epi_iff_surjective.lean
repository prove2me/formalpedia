-- Prove2me | Theorems.Thm_PretorsionImageClosed_FGModuleCat_epi_iff_surjective
-- name    : PretorsionImageClosed.FGModuleCat.epi_iff_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:34:25.170186+00:00
-- url     : https://prove2.me/theorems/feb319ca-6874-4f53-8db3-8576c1baeea4
-- title:
--   FGModule Cat: epi iff surjective
-- statement:
--   The FGModule Cat construction uses the epi iff surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/FiniteModules.lean#L46-L54
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/FiniteModules.lean#L46-L54

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

theorem PretorsionImageClosed.FGModuleCat.epi_iff_surjective {X Y : FGModuleCat R} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f.hom.hom := by sorry
