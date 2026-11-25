-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_q_eq_of_finiteIndex
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.q_eq_of_finiteIndex
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:51:26.97037+00:00
-- url     : https://prove2.me/theorems/73db922d-12c6-5855-8f5e-64e72041ed20
-- title:
--   Herbrand: q eq of finite Index
-- statement:
--   The Herbrand construction uses the q eq of finite Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HerbrandB.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HerbrandB.lean#L38-L43

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.q_eq_of_finiteIndex (hf : Injective f) (hfi : f.range.FiniteIndex)
    (fD : ∀ a, f (DA a) = DB (f a)) (fN : ∀ a, f (NA a) = NB (f a))
    (DN : ∀ b, DB (NB b) = 0) (ND : ∀ b, NB (DB b) = 0) (hA : IsFin DA NA) :
    q DA NA = q DB NB := by sorry
