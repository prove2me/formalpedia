-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_isIntegralClosure_OK
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.isIntegralClosure_OK
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T17:04:02.313212+00:00
-- url     : https://prove2.me/theorems/d04ad637-2853-4be0-875d-78ed985f2c0f
-- title:
--   Local Class Field: is Integral Closure OK
-- statement:
--   The Local Class Field construction uses the is Integral Closure OK property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsD.lean#L46-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsD.lean#L46-L50

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.isIntegralClosure_OK : IsIntegralClosure (OK p K) ℤ_[p] K := by sorry
