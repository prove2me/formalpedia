-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_multOf_mono
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.multOf_mono
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:55:24.210789+00:00
-- url     : https://prove2.me/theorems/85e40f2c-5d97-5733-a3fa-68a46ee49c39
-- title:
--   Local Class Field: mult Of mono
-- statement:
--   The Local Class Field construction uses the mult Of mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsC.lean#L80-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsC.lean#L80-L80

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.multOf_mono (h : K ≤ L) : multOf p K ≤ multOf p L := by sorry
