-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_h_rat_subsingleton
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.h_rat_subsingleton
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:56:31.886052+00:00
-- url     : https://prove2.me/theorems/69c78f4d-f3a7-5366-a732-951bc8b5d075
-- title:
--   Local Class Field: h rat subsingleton
-- statement:
--   The Local Class Field construction uses the h rat subsingleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HSubsingletonOfUniquelyDivisible.lean#L46-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HSubsingletonOfUniquelyDivisible.lean#L46-L53

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.h_rat_subsingleton [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] (n : ℕ) (hn : 0 < n) :
    Subsingleton ((trivRep G ℚ).H n) := by sorry
