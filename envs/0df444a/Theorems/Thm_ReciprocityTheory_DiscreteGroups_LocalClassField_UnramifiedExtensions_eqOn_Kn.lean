-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_eqOn_Kn
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.eqOn_Kn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:38:34.373102+00:00
-- url     : https://prove2.me/theorems/4fdfdb09-9acd-4457-a476-4585849adc10
-- title:
--   Unramified Extensions: eq On Kn
-- statement:
--   The Unramified Extensions construction uses the eq On Kn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/PowPowSuccSub.lean#L135-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/PowPowSuccSub.lean#L135-L144

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.eqOn_Kn {n : ℕ} {σ τ : GK p K}
    (h : ∀ ζ : PadicAlgCl p, ζ ^ (qK p K ^ n - 1) = 1 → σ ζ = τ ζ) {x : PadicAlgCl p} (hx : x ∈ Kn p K n) :
    σ x = τ x := by sorry
