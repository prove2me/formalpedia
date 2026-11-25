-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_vLayerMap_toLayer
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.vLayerMap_toLayer
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:46:14.434893+00:00
-- url     : https://prove2.me/theorems/c71cf6ec-a10e-5fde-9c45-08e22412e359
-- title:
--   Local Class Field: v Layer Map to Layer
-- statement:
--   The Local Class Field construction uses the v Layer Map to Layer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsE.lean#L54-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsE.lean#L54-L57

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.vLayerMap_toLayer (h : K ≤ L) [(subG p K L).Normal] (x : multOf p L) :
    vLayerMap p K L (toLayer p x) = vOn p L x := by sorry
