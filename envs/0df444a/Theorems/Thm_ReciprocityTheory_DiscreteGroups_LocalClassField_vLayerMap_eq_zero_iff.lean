-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_vLayerMap_eq_zero_iff
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.vLayerMap_eq_zero_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:46:31.861346+00:00
-- url     : https://prove2.me/theorems/178fa96e-300d-5766-9ec9-2647d9dfaca2
-- title:
--   Local Class Field: v Layer Map eq zero iff
-- statement:
--   The Local Class Field construction uses the v Layer Map eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsE.lean#L70-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsE.lean#L70-L78

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.vLayerMap_eq_zero_iff (he : 0 < eK p L) (h : K ≤ L) [(subG p K L).Normal]
    (x : (layer p K L).V) : vLayerMap p K L x = 0 ↔ x ∈ LinearMap.range (layerUIncl p K L).u := by sorry
