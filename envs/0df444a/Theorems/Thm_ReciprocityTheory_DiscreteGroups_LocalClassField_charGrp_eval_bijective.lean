-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_charGrp_eval_bijective
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.charGrp_eval_bijective
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:58:58.324817+00:00
-- url     : https://prove2.me/theorems/e36472bc-efe0-56c0-9e2a-0dad53327bc3
-- title:
--   Local Class Field: char Grp eval bijective
-- statement:
--   The Local Class Field construction uses the char Grp eval bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HSubsingletonOfUniquelyDivisible.lean#L146-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HSubsingletonOfUniquelyDivisible.lean#L146-L155

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.charGrp_eval_bijective [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] (s : G)
    (hs : IsZHat G s) : Bijective fun χ : charGrp G => χ.1 (Additive.ofMul s) := by sorry
