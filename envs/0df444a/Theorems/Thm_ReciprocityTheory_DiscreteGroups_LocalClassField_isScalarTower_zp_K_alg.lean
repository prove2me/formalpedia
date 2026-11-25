-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_isScalarTower_zp_K_alg
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.isScalarTower_zp_K_alg
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:39:49.097495+00:00
-- url     : https://prove2.me/theorems/b9fe5cd1-d444-49a8-9178-683516f1cd7f
-- title:
--   Local Class Field: is Scalar Tower zp K alg
-- statement:
--   The Local Class Field construction uses the is Scalar Tower zp K alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsD.lean#L30-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsD.lean#L30-L30

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.isScalarTower_zp_K_alg : IsScalarTower ℤ_[p] K (PadicAlgCl p) := by sorry
