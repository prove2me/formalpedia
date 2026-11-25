-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_relIndex_zmultiples_one_inv
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.relIndex_zmultiples_one_inv
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:00:00.294093+00:00
-- url     : https://prove2.me/theorems/f22f2515-1c3a-5dff-a3da-64c7becd2e6a
-- title:
--   Local Class Field: rel Index zmultiples one inv
-- statement:
--   The Local Class Field construction uses the rel Index zmultiples one inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsB.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsB.lean#L29-L33

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.relIndex_zmultiples_one_inv {n : ℕ} (hn : 0 < n) :
    (AddSubgroup.zmultiples (1 : ℝ)).relIndex (AddSubgroup.zmultiples ((n : ℝ)⁻¹)) = n := by sorry
