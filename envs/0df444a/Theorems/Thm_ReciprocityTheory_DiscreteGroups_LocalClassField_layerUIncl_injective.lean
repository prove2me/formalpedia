-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_layerUIncl_injective
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.layerUIncl_injective
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T16:46:24.339947+00:00
-- url     : https://prove2.me/theorems/6e596acf-8559-59b5-80c4-fa8e34d3b36e
-- title:
--   Local Class Field: layer UIncl injective
-- statement:
--   The Local Class Field construction uses the layer UIncl injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsE.lean#L64-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsE.lean#L64-L68

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.layerUIncl_injective [(subG p K L).Normal] : Function.Injective (layerUIncl p K L).u := by sorry
