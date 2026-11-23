-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_dHom_apply
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.dHom_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:07:05.474159+00:00
-- url     : https://prove2.me/theorems/e9b3ad92-b881-475a-aabc-9d3aefb828a3
-- title:
--   Herbrand: d Hom apply
-- statement:
--   The Herbrand construction uses the d Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HerbrandB.lean#L55-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HerbrandB.lean#L55-L55

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.dHom_apply (ρ : Representation k G M) (g : G) (x : M) : dHom ρ g x = ρ g x - x := by sorry

attribute [defeq] ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.dHom_apply
