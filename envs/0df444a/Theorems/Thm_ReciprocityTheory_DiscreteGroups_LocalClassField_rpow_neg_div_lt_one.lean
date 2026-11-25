-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_rpow_neg_div_lt_one
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.rpow_neg_div_lt_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T17:03:07.180517+00:00
-- url     : https://prove2.me/theorems/5aff6df8-1fa4-5fad-a893-d50a5e73c908
-- title:
--   Local Class Field: rpow neg div lt one
-- statement:
--   The Local Class Field construction uses the rpow neg div lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsF.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsF.lean#L14-L17

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsF
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
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.rpow_neg_div_lt_one (he : 0 < eK p K) {i : ℕ} (hi : 0 < i) : (p : ℝ) ^ (- (i : ℝ) / eK p K) < 1 := by sorry
