-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_Kn_le
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.Kn_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:38:27.999527+00:00
-- url     : https://prove2.me/theorems/1b786ff3-cbae-4a55-8286-882ee019384b
-- title:
--   Unramified Extensions: Kn le
-- statement:
--   The Unramified Extensions construction uses the Kn le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/PowPowSuccSub.lean#L107-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/PowPowSuccSub.lean#L107-L109

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.Kn_le {n : ℕ} {S : IntermediateField ℚ_[p] (PadicAlgCl p)} (h1 : K ≤ S)
    (h2 : ∀ ζ : PadicAlgCl p, ζ ^ (qK p K ^ n - 1) = 1 → ζ ∈ S) : Kn p K n ≤ S := by sorry
