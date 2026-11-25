-- Prove2me | Theorems.Thm_PretorsionImageClosed_FGModuleCat_ker_eq_bot_of_mono
-- name    : PretorsionImageClosed.FGModuleCat.ker_eq_bot_of_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:12:42.213323+00:00
-- url     : https://prove2.me/theorems/b80a89cb-6820-4232-bbe0-3f1cd1921179
-- title:
--   FGModule Cat: ker eq bot of mono
-- statement:
--   The FGModule Cat construction uses the ker eq bot of mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/FiniteModules.lean#L69-L71
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/FiniteModules.lean#L69-L71

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

theorem PretorsionImageClosed.FGModuleCat.ker_eq_bot_of_mono {X Y : FGModuleCat R} (f : X ⟶ Y) [Mono f] :
    LinearMap.ker f.hom.hom = ⊥ := by sorry
