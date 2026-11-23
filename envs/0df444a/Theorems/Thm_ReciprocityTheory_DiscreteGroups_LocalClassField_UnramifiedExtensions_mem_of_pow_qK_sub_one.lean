-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_mem_of_pow_qK_sub_one
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.mem_of_pow_qK_sub_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:29:05.798992+00:00
-- url     : https://prove2.me/theorems/b46632b4-8d67-48a9-a254-7242fb857510
-- title:
--   Unramified Extensions: mem of pow q K sub one
-- statement:
--   The Unramified Extensions construction uses the mem of pow q K sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/MemOfPowQKSubOne.lean#L103-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/MemOfPowQKSubOne.lean#L103-L129

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_NormSubEqOneOfPowEqOne
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_MemOfPowQKSubOne
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
variable {p : ℕ} [Fact p.Prime]

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.mem_of_pow_qK_sub_one (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : FiniteDimensional ℚ_[p] K)
    {ζ : PadicAlgCl p} (hζ : ζ ^ (qK p K - 1) = 1) : ζ ∈ K := by sorry
