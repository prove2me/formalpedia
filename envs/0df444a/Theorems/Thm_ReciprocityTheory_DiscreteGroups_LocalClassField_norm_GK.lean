-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_norm_GK
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.norm_GK
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:43.010325+00:00
-- url     : https://prove2.me/theorems/8cd942a7-1839-4727-baf1-91313c2c6028
-- title:
--   Local Class Field: norm GK
-- statement:
--   The Local Class Field construction uses the norm GK property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtA.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtA.lean#L21-L22

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_PowPowSuccSub
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_GK

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
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.norm_GK (σ : GK p K) (x : PadicAlgCl p) : ‖σ x‖ = ‖x‖ := by sorry
