-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_relIndex_pos_of_le_zmultiples
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.relIndex_pos_of_le_zmultiples
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:54:18.921439+00:00
-- url     : https://prove2.me/theorems/6f11e0c3-6736-5475-b467-b783e7336bda
-- title:
--   Local Class Field: rel Index pos of le zmultiples
-- statement:
--   The Local Class Field construction uses the rel Index pos of le zmultiples property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsB.lean#L62-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsB.lean#L62-L67

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.relIndex_pos_of_le_zmultiples (V : AddSubgroup ℝ) (h1 : (1 : ℝ) ∈ V) {n : ℕ} (hn : 0 < n)
    (hV : V ≤ AddSubgroup.zmultiples ((n : ℝ)⁻¹)) : 0 < (AddSubgroup.zmultiples (1 : ℝ)).relIndex V := by sorry
