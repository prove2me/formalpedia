-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_ker_Tmap_g
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.ker_Tmap_g
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:50:56.723467+00:00
-- url     : https://prove2.me/theorems/9bc25a1b-2a02-4e23-af0e-b3b7ec16f0ca
-- title:
--   Herbrand: ker Tmap g
-- statement:
--   The Herbrand construction uses the ker Tmap g property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HerbrandA.lean#L67-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HerbrandA.lean#L67-L90

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.ker_Tmap_g (h : SES DA NA DB NB DC NC f g) :
    (Tmap g h.gD h.gN).ker = (Tmap f h.fD h.fN).range := by sorry
