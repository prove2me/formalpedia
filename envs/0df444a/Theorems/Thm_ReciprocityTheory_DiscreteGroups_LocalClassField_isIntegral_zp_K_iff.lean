-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_isIntegral_zp_K_iff
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.isIntegral_zp_K_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:41:00.17166+00:00
-- url     : https://prove2.me/theorems/484e2dc9-a9c0-4f24-bb1d-b8257ccc139f
-- title:
--   Local Class Field: is Integral zp K iff
-- statement:
--   The Local Class Field construction uses the is Integral zp K iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsD.lean#L40-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsD.lean#L40-L44

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsC
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelF
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Neutral.Cmp
noncomputable section
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
attribute [local instance] zpAlgOK

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.isIntegral_zp_K_iff (x : K) :
    IsIntegral ℤ_[p] x ↔ IsIntegral (PadicInt.subring p) (x : PadicAlgCl p) := by sorry
