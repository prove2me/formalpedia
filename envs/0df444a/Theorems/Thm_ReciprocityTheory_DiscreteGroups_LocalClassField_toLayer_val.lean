-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_toLayer_val
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.toLayer_val
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:46:17.300542+00:00
-- url     : https://prove2.me/theorems/62b3de8a-dad5-5bf4-8e7a-898ad5a30a3e
-- title:
--   Local Class Field: to Layer val
-- statement:
--   The Local Class Field construction uses the to Layer val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsE.lean#L41-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsE.lean#L41-L41

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsD
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsE
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
variable (p : ℕ) [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.toLayer_val [(subG p K L).Normal] (x : multOf p L) : (toLayer p x : (layer p K L).V).1 = x.1 := by sorry
