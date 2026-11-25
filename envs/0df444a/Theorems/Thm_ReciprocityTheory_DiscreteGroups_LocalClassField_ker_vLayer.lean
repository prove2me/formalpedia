-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_ker_vLayer
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.ker_vLayer
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:46:33.07356+00:00
-- url     : https://prove2.me/theorems/dd266ace-5b4e-5a9d-8532-cb9180528790
-- title:
--   Local Class Field: ker v Layer
-- statement:
--   The Local Class Field construction uses the ker v Layer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsE.lean#L83-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsE.lean#L83-L87

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.ker_vLayer (he : 0 < eK p L) (h : K ≤ L) [(subG p K L).Normal] :
    LinearMap.ker (vLayer p K L).u = LinearMap.range (layerUIncl p K L).u := by sorry
