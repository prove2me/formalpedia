-- Prove2me | Theorems.Thm_PretorsionImageClosed_FGModuleCat_isZero_iff_subsingleton
-- name    : PretorsionImageClosed.FGModuleCat.isZero_iff_subsingleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:34:23.035466+00:00
-- url     : https://prove2.me/theorems/2dae2591-d02d-40f2-b3c6-4cb379b3a1fb
-- title:
--   FGModule Cat: is Zero iff subsingleton
-- statement:
--   The FGModule Cat construction uses the is Zero iff subsingleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/FiniteModules.lean#L86-L96
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/FiniteModules.lean#L86-L96

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

theorem PretorsionImageClosed.FGModuleCat.isZero_iff_subsingleton (X : FGModuleCat R) : IsZero X ↔ Subsingleton X := by sorry
