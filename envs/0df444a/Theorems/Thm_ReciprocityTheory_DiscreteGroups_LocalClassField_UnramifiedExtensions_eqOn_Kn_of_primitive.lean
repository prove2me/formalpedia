-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_eqOn_Kn_of_primitive
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.eqOn_Kn_of_primitive
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:23.528158+00:00
-- url     : https://prove2.me/theorems/d8b90745-e71a-43ae-99d8-4910f3e2e1b9
-- title:
--   Unramified Extensions: eq On Kn of primitive
-- statement:
--   The Unramified Extensions construction uses the eq On Kn of primitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtD.lean#L25-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtD.lean#L25-L31

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtC
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD
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
open ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.eqOn_Kn_of_primitive {n : ℕ} (h0 : qK p K ^ n - 1 ≠ 0) {ζ₀ : PadicAlgCl p}
    (hζ₀ : IsPrimitiveRoot ζ₀ (qK p K ^ n - 1)) {σ τ : GK p K} (h : σ ζ₀ = τ ζ₀) {x : PadicAlgCl p}
    (hx : x ∈ Kn p K n) : σ x = τ x := by sorry
