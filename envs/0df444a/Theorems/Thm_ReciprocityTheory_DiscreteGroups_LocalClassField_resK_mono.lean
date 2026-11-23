-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_resK_mono
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.resK_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:09.919255+00:00
-- url     : https://prove2.me/theorems/70e833b2-0b65-4da9-aad4-0f9da1cb5e8f
-- title:
--   Local Class Field: res K mono
-- statement:
--   The Local Class Field construction uses the res K mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtA.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtA.lean#L18-L19

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_PowPowSuccSub
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_resK_mono

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.resK_mono {K L : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ L) : resK p K ≤ resK p L := by sorry
