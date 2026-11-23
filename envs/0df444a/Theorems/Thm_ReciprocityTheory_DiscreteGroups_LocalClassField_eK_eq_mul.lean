-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_eK_eq_mul
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.eK_eq_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:07:50.435872+00:00
-- url     : https://prove2.me/theorems/c92d57e8-4ff7-4146-b7f5-bc3b311e164a
-- title:
--   Local Class Field: e K eq mul
-- statement:
--   The Local Class Field construction uses the e K eq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsC.lean#L90-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsC.lean#L90-L90

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsB
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh
noncomputable section
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
variable {K L}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.eK_eq_mul (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) : eK p L = eLK p K L * eK p K := by sorry
