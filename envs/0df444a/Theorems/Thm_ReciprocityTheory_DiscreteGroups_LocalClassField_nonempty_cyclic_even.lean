-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_nonempty_cyclic_even
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.nonempty_cyclic_even
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:49:22.425995+00:00
-- url     : https://prove2.me/theorems/3e294088-7871-46a4-b85c-eea31d1d7c3e
-- title:
--   Local Class Field: nonempty cyclic even
-- statement:
--   The Local Class Field construction uses the nonempty cyclic even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/FinCoh.lean#L161-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/FinCoh.lean#L161-L173

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.nonempty_cyclic_even (M : TRep R C) (g : C) (hg : ∀ x, x ∈ Subgroup.zpowers g) (i : ℕ) (h0 : i ≠ 0)
    (hi : Even i) :
    Nonempty (M.H i ≃ₗ[R] (M.rho.invariants ⧸
      (LinearMap.range M.rho.norm).comap M.rho.invariants.subtype)) := by sorry
