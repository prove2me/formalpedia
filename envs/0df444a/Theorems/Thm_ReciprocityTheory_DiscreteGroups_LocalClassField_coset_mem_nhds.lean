-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_coset_mem_nhds
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.coset_mem_nhds
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:07:42.159807+00:00
-- url     : https://prove2.me/theorems/fc53c035-8494-446e-98b0-455e2da930c6
-- title:
--   Local Class Field: coset mem nhds
-- statement:
--   The Local Class Field construction uses the coset mem nhds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GabLim.lean#L148-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GabLim.lean#L148-L153

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GabLim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh Function
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
open Topology
open scoped commutatorElement
variable {p K L}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.coset_mem_nhds (hL : IsAbLK p K L) (g : GK p K) :
    toAbK p K '' {g' | g⁻¹ * g' ∈ subG p K L} ∈ 𝓝 (toAbK p K g) := by sorry
