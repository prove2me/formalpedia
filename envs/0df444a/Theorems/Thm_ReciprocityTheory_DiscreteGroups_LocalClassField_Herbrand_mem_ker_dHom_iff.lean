-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_mem_ker_dHom_iff
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.mem_ker_dHom_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:18.060795+00:00
-- url     : https://prove2.me/theorems/08b2c19d-5eea-4fc9-ba2b-652ab695c061
-- title:
--   Herbrand: mem ker d Hom iff
-- statement:
--   The Herbrand construction uses the mem ker d Hom iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HerbrandB.lean#L69-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HerbrandB.lean#L69-L73

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.mem_ker_dHom_iff (ρ : Representation k G M) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (x : M) :
    x ∈ (dHom ρ g).ker ↔ ∀ c : G, ρ c x = x := by sorry
