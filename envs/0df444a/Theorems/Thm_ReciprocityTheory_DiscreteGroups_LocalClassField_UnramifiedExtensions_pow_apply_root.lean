-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_pow_apply_root
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.pow_apply_root
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:09.597685+00:00
-- url     : https://prove2.me/theorems/c91ae7f5-a219-4035-b35c-ad02bcb2e7e9
-- title:
--   Unramified Extensions: pow apply root
-- statement:
--   The Unramified Extensions construction uses the pow apply root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtD.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtD.lean#L16-L23

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.pow_apply_root {n : ℕ} {φ : GK p K}
    (h : ∀ ζ : PadicAlgCl p, ζ ^ (qK p K ^ n - 1) = 1 → φ ζ = ζ ^ qK p K) (i : ℕ) :
    ∀ ζ : PadicAlgCl p, ζ ^ (qK p K ^ n - 1) = 1 → (φ ^ i) ζ = ζ ^ (qK p K ^ i) := by sorry
