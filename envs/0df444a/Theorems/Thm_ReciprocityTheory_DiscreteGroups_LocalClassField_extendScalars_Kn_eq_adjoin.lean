-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_extendScalars_Kn_eq_adjoin
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.extendScalars_Kn_eq_adjoin
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:59:59.447801+00:00
-- url     : https://prove2.me/theorems/ef41155b-2743-470d-a991-5cc4ab9de676
-- title:
--   Local Class Field: extend Scalars Kn eq adjoin
-- statement:
--   The Local Class Field construction uses the extend Scalars Kn eq adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtC.lean#L25-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtC.lean#L25-L40

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtB
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtC
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_le_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_le_Kn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 Polynomial
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.extendScalars_Kn_eq_adjoin {n : ℕ} {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ (qK p K ^ n - 1))
    (hm : qK p K ^ n - 1 ≠ 0) :
    IntermediateField.extendScalars (le_Kn p K n) = IntermediateField.adjoin K {ζ} := by sorry
