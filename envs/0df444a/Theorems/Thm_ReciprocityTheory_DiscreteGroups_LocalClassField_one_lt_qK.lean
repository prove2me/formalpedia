-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_one_lt_qK
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.one_lt_qK
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:54:07.09033+00:00
-- url     : https://prove2.me/theorems/1b88046d-23e9-4b26-83b8-8f7399e2c635
-- title:
--   Local Class Field: one lt q K
-- statement:
--   The Local Class Field construction uses the one lt q K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtA.lean#L30-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtA.lean#L30-L31

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_PowPowSuccSub
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_one_lt_qK

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.one_lt_qK (hK : FiniteDimensional ℚ_[p] K) : 1 < qK p K := by sorry
