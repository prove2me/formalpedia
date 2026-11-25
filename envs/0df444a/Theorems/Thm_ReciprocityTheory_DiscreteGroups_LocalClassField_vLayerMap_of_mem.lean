-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_vLayerMap_of_mem
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.vLayerMap_of_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T16:49:31.409966+00:00
-- url     : https://prove2.me/theorems/d01aed03-6f35-4966-86f4-b8ce1355870b
-- title:
--   Local Class Field: v Layer Map of mem
-- statement:
--   The Local Class Field construction uses the v Layer Map of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsE.lean#L89-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsE.lean#L89-L95

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.vLayerMap_of_mem (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) [(subG p K L).Normal]
    (x : (layer p K L).V) (hx : x.1 ∈ multOf p K) :
    vLayerMap p K L x = eLK p K L * vOn p K ⟨x.1, hx⟩ := by sorry
