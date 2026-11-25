-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_norm_Kn
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.norm_Kn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:55:36.337947+00:00
-- url     : https://prove2.me/theorems/9c9c64ef-ee70-4c90-b4be-c18ca4f510a0
-- title:
--   Local Class Field: norm Kn
-- statement:
--   The Local Class Field construction uses the norm Kn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtC.lean#L127-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtC.lean#L127-L129

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtB
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 Polynomial
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.norm_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) {x : PadicAlgCl p}
    (hx : x ∈ Kn p K n) : ∃ y ∈ K, ‖x‖ = ‖y‖ := by sorry
