-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_isFin_of_finite
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.isFin_of_finite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:07:54.969599+00:00
-- url     : https://prove2.me/theorems/e63f4a31-7641-4617-9e50-afb4e2c49fad
-- title:
--   Herbrand: is Fin of finite
-- statement:
--   The Herbrand construction uses the is Fin of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HerbrandA.lean#L241-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HerbrandA.lean#L241-L241

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.isFin_of_finite [Finite M] (D N : M →+ M) : IsFin D N := by sorry
