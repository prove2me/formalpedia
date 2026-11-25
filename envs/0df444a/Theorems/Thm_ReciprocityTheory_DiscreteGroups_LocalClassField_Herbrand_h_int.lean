-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_h_int
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.h_int
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:51:03.270381+00:00
-- url     : https://prove2.me/theorems/aca6611f-5a68-4948-b770-15a26bc0126b
-- title:
--   Herbrand: h int
-- statement:
--   The Herbrand construction uses the h int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HerbrandB.lean#L131-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HerbrandB.lean#L131-L159

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.h_int (ρ : Representation ℤ G ℤ) (hρ : ∀ c x, ρ c x = x) (g : G) :
    HFin ρ g ∧ Nat.card (TateZerothCohomology ρ g) = Nat.card G ∧ Subsingleton (H1 ρ g) ∧ h ρ g = Nat.card G := by sorry
