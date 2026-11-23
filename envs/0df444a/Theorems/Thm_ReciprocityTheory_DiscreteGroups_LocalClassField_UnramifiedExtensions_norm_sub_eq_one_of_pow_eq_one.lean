-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_sub_eq_one_of_pow_eq_one
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.norm_sub_eq_one_of_pow_eq_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:27:21.071474+00:00
-- url     : https://prove2.me/theorems/85d17a96-8f70-4c14-9869-a1b1133b676d
-- title:
--   Unramified Extensions: norm sub eq one of pow eq one
-- statement:
--   The Unramified Extensions construction uses the norm sub eq one of pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/NormSubEqOneOfPowEqOne.lean#L142-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/NormSubEqOneOfPowEqOne.lean#L142-L151

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrDefs
import Definitions.Def_Lemmata_PadicNatCastNorm_NormNatCastOfNotDvd
import Definitions.Def_Lemmata_FirstBlockLemmaC_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaD_Imports
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_NormSubEqOneOfPowEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
open _root_.Neutral.B1 ReciprocityTheory.DiscreteGroups.LocalClassField
variable {p : ℕ} [Fact p.Prime]

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.norm_sub_eq_one_of_pow_eq_one {m : ℕ} (hm : ¬ p ∣ m) {ζ ξ : PadicAlgCl p} (hζ : ζ ^ m = 1)
    (hξ : ξ ^ m = 1) (h : ζ ≠ ξ) : ‖ζ - ξ‖ = 1 := by sorry
