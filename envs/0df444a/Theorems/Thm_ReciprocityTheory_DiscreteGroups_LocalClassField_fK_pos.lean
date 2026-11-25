-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_fK_pos
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.fK_pos
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:40:57.56565+00:00
-- url     : https://prove2.me/theorems/d6110b37-9c67-4fb6-92a5-57b31378e6b0
-- title:
--   Local Class Field: f K pos
-- statement:
--   The Local Class Field construction uses the f K pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsD.lean#L155-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsD.lean#L155-L157

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsC
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelF
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Neutral.Cmp
noncomputable section
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
attribute [local instance] zpAlgOK

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.fK_pos (hK : FiniteDimensional ℚ_[p] K) : 0 < fK p K := by sorry
