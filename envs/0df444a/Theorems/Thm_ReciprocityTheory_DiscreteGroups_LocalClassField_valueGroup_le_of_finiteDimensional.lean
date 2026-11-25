-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_valueGroup_le_of_finiteDimensional
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.valueGroup_le_of_finiteDimensional
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:55:41.103436+00:00
-- url     : https://prove2.me/theorems/2db8d529-fa1c-55ee-9ce3-b89123bebc10
-- title:
--   Local Class Field: value Group le of finite Dimensional
-- statement:
--   The Local Class Field construction uses the value Group le of finite Dimensional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsB.lean#L96-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsB.lean#L96-L125

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsB
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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.valueGroup_le_of_finiteDimensional (hK : FiniteDimensional ℚ_[p] K) :
    valueGroup p K ≤ AddSubgroup.zmultiples
      ((Module.finrank (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p))
        (IntermediateField.extendScalars (bot_le : ⊥ ≤ K)) : ℝ)⁻¹) := by sorry
