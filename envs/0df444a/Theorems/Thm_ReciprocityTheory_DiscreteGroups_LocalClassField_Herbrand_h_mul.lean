-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_h_mul
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.h_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:51:12.268814+00:00
-- url     : https://prove2.me/theorems/9d221cdc-8651-4cbb-ab9e-5f0d4d2a3c31
-- title:
--   Herbrand: h mul
-- statement:
--   The Herbrand construction uses the h mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HerbrandB.lean#L105-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HerbrandB.lean#L105-L110

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
variable {k G M : Type*} [CommRing k] [Group G] [Fintype G] [AddCommGroup M] [Module k M]
variable {A B C : Type*} [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  [AddCommGroup C] [Module k C]

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.h_mul (ρA : Representation k G A) (ρB : Representation k G B) (ρC : Representation k G C)
    (g : G) (i : A →+ B) (p : B →+ C) (hi : Injective i) (hip : Function.Exact i p) (hp : Surjective p)
    (hiG : ∀ c a, i (ρA c a) = ρB c (i a)) (hpG : ∀ c b, p (ρB c b) = ρC c (p b))
    (hA : HFin ρA g) (hC : HFin ρC g) : HFin ρB g ∧ h ρB g = h ρA g * h ρC g := by sorry
