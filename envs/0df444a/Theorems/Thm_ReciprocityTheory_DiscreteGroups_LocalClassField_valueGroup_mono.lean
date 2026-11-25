-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_valueGroup_mono
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.valueGroup_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:07.327578+00:00
-- url     : https://prove2.me/theorems/cf2fdf76-75e8-4f59-99ab-7b8b5908a606
-- title:
--   Local Class Field: value Group mono
-- statement:
--   The Local Class Field construction uses the value Group mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsC.lean#L82-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsC.lean#L82-L82

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsB
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh
noncomputable section
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
variable {K L}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.valueGroup_mono (h : K ≤ L) : valueGroup p K ≤ valueGroup p L := by sorry
