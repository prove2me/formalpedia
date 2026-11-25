-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_coe_sum_KbarMult
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.coe_sum_KbarMult
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:59:41.124325+00:00
-- url     : https://prove2.me/theorems/2d9912b6-7f9b-4d28-8a36-f08364ed7906
-- title:
--   Local Class Field: coe sum Kbar Mult
-- statement:
--   The Local Class Field construction uses the coe sum Kbar Mult property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/NormOpenA.lean#L162-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/NormOpenA.lean#L162-L171

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_NormOpenA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh Function
variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.coe_sum_KbarMult {ι : Type*} (s : Finset ι) (f : ι → KbarMult p) :
    ((Additive.toMul (∑ c ∈ s, f c) : (PadicAlgCl p)ˣ) : PadicAlgCl p) =
      ∏ c ∈ s, ((Additive.toMul (f c) : (PadicAlgCl p)ˣ) : PadicAlgCl p) := by sorry
