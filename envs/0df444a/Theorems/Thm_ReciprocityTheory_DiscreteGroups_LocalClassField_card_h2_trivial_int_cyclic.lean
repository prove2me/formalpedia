-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_card_h2_trivial_int_cyclic
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.card_h2_trivial_int_cyclic
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:06:02.566432+00:00
-- url     : https://prove2.me/theorems/31b16340-23ef-4ac7-9fad-738da9d3bf65
-- title:
--   Local Class Field: card h2 trivial int cyclic
-- statement:
--   The Local Class Field construction uses the card h2 trivial int cyclic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/BrUnrA.lean#L70-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/BrUnrA.lean#L70-L112

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_ImportsAlt
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HSubsingletonOfUniquelyDivisible
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_FinCoh
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_BrUnrA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Gal Function
noncomputable section

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.card_h2_trivial_int_cyclic (C : Type) [Group C] [Finite C] [TopologicalSpace C] [IsTopologicalGroup C]
    [DiscreteTopology C] (g : C) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Nat.card ((trivRep C ℤ).H 2) = Nat.card C := by sorry
