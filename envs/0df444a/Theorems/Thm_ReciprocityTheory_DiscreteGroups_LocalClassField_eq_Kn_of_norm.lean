-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_eq_Kn_of_norm
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.eq_Kn_of_norm
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:53:08.928516+00:00
-- url     : https://prove2.me/theorems/1c056aab-2725-423f-9eff-0df957a415a3
-- title:
--   Local Class Field: eq Kn of norm
-- statement:
--   The Local Class Field construction uses the eq Kn of norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtE.lean#L67-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtE.lean#L67-L98

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtC
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtE
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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.eq_Kn_of_norm (hK : FiniteDimensional ℚ_[p] K) {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hKL : K ≤ L) {n : ℕ} (hn : 0 < n)
    (hdeg : Module.finrank ℚ_[p] L = n * Module.finrank ℚ_[p] K)
    (h : ∀ x ∈ L, ∃ y ∈ K, ‖x‖ = ‖y‖) : L = Kn p K n := by sorry
