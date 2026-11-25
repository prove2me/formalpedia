-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_exists_pow_of_GK
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.exists_pow_of_GK
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:38:34.853807+00:00
-- url     : https://prove2.me/theorems/d0ae9cc7-10cb-4e4c-bea9-d4ca31cb5f9a
-- title:
--   Unramified Extensions: exists pow of GK
-- statement:
--   The Unramified Extensions construction uses the exists pow of GK property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/PowPowSuccSub.lean#L45-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/PowPowSuccSub.lean#L45-L98

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.exists_pow_of_GK (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) (σ : GK p K)
    {ζ : PadicAlgCl p} (hζ : ζ ^ (qK p K ^ n - 1) = 1) : ∃ i < n, σ ζ = ζ ^ (qK p K ^ i) := by sorry
