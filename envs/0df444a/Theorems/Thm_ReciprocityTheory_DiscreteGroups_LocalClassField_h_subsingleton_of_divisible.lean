-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_h_subsingleton_of_divisible
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.h_subsingleton_of_divisible
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:56:25.39479+00:00
-- url     : https://prove2.me/theorems/d8b700d5-831f-57b0-b795-3c512080b941
-- title:
--   Local Class Field: h subsingleton of divisible
-- statement:
--   The Local Class Field construction uses the h subsingleton of divisible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HSubsingletonOfUniquelyDivisible.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HSubsingletonOfUniquelyDivisible.lean#L41-L44

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
import Definitions.Def_ReciprocityTheory_GroupCohomology_ImportsAlt
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_QZDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_MemZmultiplesOfAddOrderOf
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HSubsingletonOfUniquelyDivisible
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
variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.h_subsingleton_of_divisible [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (M : TRep ℤ G) [DiscreteTopology M.V] (hM : ∀ k : ℕ, 0 < k → Bijective fun m : M.V => k • m)
    (n : ℕ) (hn : 0 < n) : Subsingleton (M.H n) := by sorry
