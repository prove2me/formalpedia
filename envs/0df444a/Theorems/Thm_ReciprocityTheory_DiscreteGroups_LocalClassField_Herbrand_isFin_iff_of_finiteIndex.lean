-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_isFin_iff_of_finiteIndex
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.isFin_iff_of_finiteIndex
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:50:54.274904+00:00
-- url     : https://prove2.me/theorems/65716f1a-8e5e-4957-b304-bcf7d82a2073
-- title:
--   Herbrand: is Fin iff of finite Index
-- statement:
--   The Herbrand construction uses the is Fin iff of finite Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HerbrandB.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HerbrandB.lean#L32-L36

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandB
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
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    {DA NA : A →+ A} {DB NB : B →+ B} {f : A →+ B}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.isFin_iff_of_finiteIndex (hf : Injective f) (hfi : f.range.FiniteIndex)
    (fD : ∀ a, f (DA a) = DB (f a)) (fN : ∀ a, f (NA a) = NB (f a))
    (DN : ∀ b, DB (NB b) = 0) (ND : ∀ b, NB (DB b) = 0) : IsFin DA NA ↔ IsFin DB NB := by sorry
