-- Prove2me | Theorems.Thm_PI_AddIntG_Wk_dv_coeff_mul_eq_zero_of_lt_order
-- name    : PI.AddIntG.Wk.dv_coeff_mul_eq_zero_of_lt_order
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:22:50.873825+00:00
-- url     : https://prove2.me/theorems/617f30c2-93e4-582b-9942-9df3a811993b
-- title:
--   Wk: dv coeff mul eq zero of lt order
-- statement:
--   The Wk construction uses the dv coeff mul eq zero of lt order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/DvCoeffMulEqZeroOfLtOrder.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/DvCoeffMulEqZeroOfLtOrder.lean#L20-L23

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

theorem PI.AddIntG.Wk.dv_coeff_mul_eq_zero_of_lt_order {R : Type*} [CommRing R] {σ : Type*} (f g : MvPowerSeries σ R)
    (e : σ →₀ ℕ) (h : (e.degree : ℕ∞) < f.order) : MvPowerSeries.coeff e (f * g) = 0 := by sorry
