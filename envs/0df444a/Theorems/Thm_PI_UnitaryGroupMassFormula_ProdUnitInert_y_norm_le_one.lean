-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ProdUnitInert_y_norm_le_one
-- name    : PI.UnitaryGroupMassFormula.ProdUnitInert.y_norm_le_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:32:27.285984+00:00
-- url     : https://prove2.me/theorems/79250f59-6d86-476d-ab7e-26a73a53871c
-- title:
--   Prod Unit Inert: y norm le one
-- statement:
--   The Prod Unit Inert construction uses the y norm le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertUnitProduct/NatCastNormLeOne.lean#L23-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertUnitProduct/NatCastNormLeOne.lean#L23-L55

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

theorem PI.UnitaryGroupMassFormula.ProdUnitInert.y_norm_le_one (d : ℕ) (hd : ¬ IsSquare (((-(d : ℤ) : ℤ) : ZMod p))) (X Y : ℚ_[p])
    (h : X ^ 2 + d * Y ^ 2 = 1) : ‖Y‖ ≤ 1 := by sorry
