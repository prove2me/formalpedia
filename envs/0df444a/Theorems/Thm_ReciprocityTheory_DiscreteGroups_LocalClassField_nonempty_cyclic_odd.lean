-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_nonempty_cyclic_odd
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.nonempty_cyclic_odd
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:50:38.254843+00:00
-- url     : https://prove2.me/theorems/3b362a02-84d6-4140-89ac-f1a681e735aa
-- title:
--   Local Class Field: nonempty cyclic odd
-- statement:
--   The Local Class Field construction uses the nonempty cyclic odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/FinCoh.lean#L175-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/FinCoh.lean#L175-L180

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_IsLowExists
import Definitions.Def_ReciprocityTheory_GroupCohomology_LowNat
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_FinCoh
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open ReciprocityTheory.Coh CategoryTheory
noncomputable section
universe u
variable {R : Type u} [CommRing R]
variable {C : Type u} [CommGroup C] [Fintype C] [TopologicalSpace C] [IsTopologicalGroup C]
  [DiscreteTopology C]

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.nonempty_cyclic_odd (M : TRep R C) (g : C) (hg : ∀ x, x ∈ Subgroup.zpowers g) (i : ℕ) (hi : Odd i) :
    Nonempty (M.H i ≃ₗ[R] (LinearMap.ker M.rho.norm ⧸
      (LinearMap.range (M.rho g - LinearMap.id)).comap (LinearMap.ker M.rho.norm).subtype)) := by sorry
