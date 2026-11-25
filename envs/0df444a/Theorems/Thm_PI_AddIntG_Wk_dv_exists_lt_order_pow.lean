-- Prove2me | Theorems.Thm_PI_AddIntG_Wk_dv_exists_lt_order_pow
-- name    : PI.AddIntG.Wk.dv_exists_lt_order_pow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:21:50.652265+00:00
-- url     : https://prove2.me/theorems/39c00670-4356-4d58-a7bf-003c6cd0aea2
-- title:
--   Wk: dv exists lt order pow
-- statement:
--   The Wk construction uses the dv exists lt order pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/DvCoeffMulEqZeroOfLtOrder.lean#L11-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/DvCoeffMulEqZeroOfLtOrder.lean#L11-L18

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GuLine
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DvCoeffMulEqZeroOfLtOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.AddIntG PI.AddIntG.Wk
variable {p : ℕ} [Fact p.Prime]

theorem PI.AddIntG.Wk.dv_exists_lt_order_pow {R : Type*} [CommRing R] {σ : Type*} {a : MvPowerSeries σ R}
    (ha : PowerSeries.HasSubst a) (N : ℕ) : ∃ m : ℕ, (N : ℕ∞) < (a ^ m).order := by sorry
