-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_IsTwoCocycle_sub
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2.IsTwoCocycle.sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:56.048327+00:00
-- url     : https://prove2.me/theorems/5394e92f-914d-4d01-a785-2594ab8f5fd9
-- title:
--   Is Two Cocycle: sub
-- statement:
--   The Is Two Cocycle construction uses the sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/IsTwoCocycleCoboundary.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/IsTwoCocycleCoboundary.lean#L19-L25

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_ComapZeroCoboundariesEqBot
import Definitions.Def_ReciprocityTheory_GroupCohomology_PartialProdCoe
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_IsTwoCocycleCoboundary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
variable {R : Type*} [CommRing R] {G : Type*} [Group G] {A : Type*} [AddCommGroup A] [Module R A]
  (ρ : Representation R G A) (N : Subgroup G)
variable {ρ}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2.IsTwoCocycle.sub {c c' : G → G → A} (hc : IsTwoCocycle ρ c) (hc' : IsTwoCocycle ρ c') :
    IsTwoCocycle ρ (fun g h => c g h - c' g h) := by sorry
