-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_norm_eq_rpow_vK
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.norm_eq_rpow_vK
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:07:40.386582+00:00
-- url     : https://prove2.me/theorems/fd6aec31-b897-57cd-a40c-7a7ec240f0e3
-- title:
--   Local Class Field: norm eq rpow v K
-- statement:
--   The Local Class Field construction uses the norm eq rpow v K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsC.lean#L55-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsC.lean#L55-L57

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.norm_eq_rpow_vK (hK : FiniteDimensional ℚ_[p] K) (x : Kˣ) :
    ‖((x : K) : PadicAlgCl p)‖ = (p : ℝ) ^ (- (vK p K x : ℝ) / eK p K) := by sorry
