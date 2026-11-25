-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_norm_sub_eq_one_of_pow_eq_one
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.norm_sub_eq_one_of_pow_eq_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:31:00.817368+00:00
-- url     : https://prove2.me/theorems/e2d64f76-6f79-4955-b52f-14fdcbb3fa9f
-- title:
--   Local Class Field: norm sub eq one of pow eq one
-- statement:
--   The Local Class Field construction uses the norm sub eq one of pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtA.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtA.lean#L33-L35

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_PowPowSuccSub
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_sub_eq_one_of_pow_eq_one

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.norm_sub_eq_one_of_pow_eq_one {m : ℕ} (hm : ¬ p ∣ m) {ζ ξ : PadicAlgCl p} (hζ : ζ ^ m = 1)
    (hξ : ξ ^ m = 1) (h : ζ ≠ ξ) : ‖ζ - ξ‖ = 1 := by sorry
