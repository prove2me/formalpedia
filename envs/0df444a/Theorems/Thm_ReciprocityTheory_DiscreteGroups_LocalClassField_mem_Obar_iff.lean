-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_Obar_iff
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:45.813155+00:00
-- url     : https://prove2.me/theorems/71c8cda3-1841-4f51-be71-236775201e1f
-- title:
--   Local Class Field: mem Obar iff
-- statement:
--   The Local Class Field construction uses the mem Obar iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrDefs.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrDefs.lean#L15-L17

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1
variable (p : ℕ) [Fact p.Prime]
variable {p}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff {x : PadicAlgCl p} : x ∈ Obar p ↔ ‖x‖ ≤ 1 := by sorry
