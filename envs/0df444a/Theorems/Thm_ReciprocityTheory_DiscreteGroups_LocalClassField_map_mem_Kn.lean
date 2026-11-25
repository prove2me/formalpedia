-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_map_mem_Kn
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.map_mem_Kn
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:54:55.460961+00:00
-- url     : https://prove2.me/theorems/7f12aabd-1219-4158-92b2-768d2311eb62
-- title:
--   Local Class Field: map mem Kn
-- statement:
--   The Local Class Field construction uses the map mem Kn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtA.lean#L51-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtA.lean#L51-L52

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_PowPowSuccSub
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_map_mem_Kn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.map_mem_Kn (n : ℕ) (σ : GK p K) {x : PadicAlgCl p} (hx : x ∈ Kn p K n) : σ x ∈ Kn p K n := by sorry
