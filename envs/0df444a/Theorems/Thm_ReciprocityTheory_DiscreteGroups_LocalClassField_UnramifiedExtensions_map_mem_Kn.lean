-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_map_mem_Kn
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.map_mem_Kn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:36:36.896331+00:00
-- url     : https://prove2.me/theorems/be1b0089-ec75-4a78-a821-5986a4b721e3
-- title:
--   Unramified Extensions: map mem Kn
-- statement:
--   The Unramified Extensions construction uses the map mem Kn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/PowPowSuccSub.lean#L111-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/PowPowSuccSub.lean#L111-L123

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_MemOfPowQKSubOne
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_PowPowSuccSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
open _root_.Neutral.B1 ReciprocityTheory.DiscreteGroups.LocalClassField Polynomial
variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
variable (K)

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.map_mem_Kn (n : ℕ) (σ : GK p K) {x : PadicAlgCl p} (hx : x ∈ Kn p K n) : σ x ∈ Kn p K n := by sorry
