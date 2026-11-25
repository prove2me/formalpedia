-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_isFin_left
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.isFin_left
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:50:46.911801+00:00
-- url     : https://prove2.me/theorems/62bc30bc-3a57-5b58-90e5-9947c33b3195
-- title:
--   Herbrand: is Fin left
-- statement:
--   The Herbrand construction uses the is Fin left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HerbrandA.lean#L217-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HerbrandA.lean#L217-L223

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.isFin_left (h : SES DA NA DB NB DC NC f g) (hB : IsFin DB NB) (hC : IsFin DC NC) :
    IsFin DA NA := by sorry
