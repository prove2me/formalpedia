-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_h_of_subsingleton
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.h_of_subsingleton
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:50:55.011086+00:00
-- url     : https://prove2.me/theorems/4647d736-5a7e-4d8b-a0b3-8fc42c35c888
-- title:
--   Herbrand: h of subsingleton
-- statement:
--   The Herbrand construction uses the h of subsingleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HerbrandB.lean#L120-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HerbrandB.lean#L120-L124

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.h_of_subsingleton (ρ : Representation k G M) (g : G) [Subsingleton (TateZerothCohomology ρ g)]
    [Subsingleton (H1 ρ g)] : HFin ρ g ∧ h ρ g = 1 := by sorry
