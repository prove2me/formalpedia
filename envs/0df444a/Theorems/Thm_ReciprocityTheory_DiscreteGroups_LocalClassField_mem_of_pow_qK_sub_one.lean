-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_of_pow_qK_sub_one
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.mem_of_pow_qK_sub_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:48:30.964801+00:00
-- url     : https://prove2.me/theorems/6cb85ca5-3daa-41df-8eef-5e1093c51e27
-- title:
--   Local Class Field: mem of pow q K sub one
-- statement:
--   The Local Class Field construction uses the mem of pow q K sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtA.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtA.lean#L41-L43

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_PowPowSuccSub
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_mem_of_pow_qK_sub_one

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.mem_of_pow_qK_sub_one (hK : FiniteDimensional ℚ_[p] K) {ζ : PadicAlgCl p}
    (hζ : ζ ^ (qK p K - 1) = 1) : ζ ∈ K := by sorry
