-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_half_hexagon
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.half_hexagon
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:50.277704+00:00
-- url     : https://prove2.me/theorems/fd32b155-91df-4be5-98bf-e43d406f44fa
-- title:
--   Herbrand: half hexagon
-- statement:
--   The Herbrand construction uses the half hexagon property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HerbrandA.lean#L133-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HerbrandA.lean#L133-L173

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.half_hexagon (h : SES DA NA DB NB DC NC f g) :
    ∃ δ : T DC NC →+ T NA DA, (Tmap g h.gD h.gN).ker = (Tmap f h.fD h.fN).range ∧
      δ.ker = (Tmap g h.gD h.gN).range ∧ (Tmap f h.fN h.fD).ker = δ.range := by sorry
