-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_kerMap_coe
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.kerMap_coe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:43.530797+00:00
-- url     : https://prove2.me/theorems/b1294e1c-9cf6-49f4-8c86-fa11cb0968c0
-- title:
--   Herbrand: ker Map coe
-- statement:
--   The Herbrand construction uses the ker Map coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HerbrandA.lean#L45-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HerbrandA.lean#L45-L46

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
open Function
variable {M : Type*} [AddCommGroup M]
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    {DA NA : A →+ A} {DB NB : B →+ B} {DC NC : C →+ C} {f : A →+ B} {g : B →+ C}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.kerMap_coe (f : A →+ B) (fD : ∀ a, f (DA a) = DB (f a)) (a : DA.ker) :
    ((kerMap f fD a : DB.ker) : B) = f a := by sorry

attribute [defeq] ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.kerMap_coe
