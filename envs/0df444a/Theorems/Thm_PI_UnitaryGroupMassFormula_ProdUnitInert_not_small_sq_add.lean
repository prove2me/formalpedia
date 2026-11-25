-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ProdUnitInert_not_small_sq_add
-- name    : PI.UnitaryGroupMassFormula.ProdUnitInert.not_small_sq_add
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:32:43.879978+00:00
-- url     : https://prove2.me/theorems/2e826e95-6c60-4b6b-8951-b20b75611b92
-- title:
--   Prod Unit Inert: not small sq add
-- statement:
--   The Prod Unit Inert construction uses the not small sq add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertUnitProduct/NatCastNormLeOne.lean#L9-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertUnitProduct/NatCastNormLeOne.lean#L9-L18

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertUnitProduct_NatCastNormLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ProdUnitInert
variable {p : ℕ} [Fact p.Prime]

theorem PI.UnitaryGroupMassFormula.ProdUnitInert.not_small_sq_add (d : ℕ) (hd : ¬ IsSquare (((-(d : ℤ) : ℤ) : ZMod p))) (t : ℤ_[p]) :
    ¬ ‖t ^ 2 + (d : ℤ_[p])‖ < 1 := by sorry
