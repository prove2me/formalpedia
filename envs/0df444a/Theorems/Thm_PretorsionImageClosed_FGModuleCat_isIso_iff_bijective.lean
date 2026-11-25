-- Prove2me | Theorems.Thm_PretorsionImageClosed_FGModuleCat_isIso_iff_bijective
-- name    : PretorsionImageClosed.FGModuleCat.isIso_iff_bijective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:57:34.160811+00:00
-- url     : https://prove2.me/theorems/daef2c0a-785b-4e3b-8f44-a0b0a6645fad
-- title:
--   FGModule Cat: is Iso iff bijective
-- statement:
--   The FGModule Cat construction uses the is Iso iff bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/FiniteModules.lean#L56-L63
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/FiniteModules.lean#L56-L63

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

theorem PretorsionImageClosed.FGModuleCat.isIso_iff_bijective {X Y : FGModuleCat R} (f : X ⟶ Y) : IsIso f ↔ Function.Bijective f.hom.hom := by sorry
