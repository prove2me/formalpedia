-- Prove2me | Theorems.Thm_PI_AddIntG_Wk_dv_pderiv_subst_coe
-- name    : PI.AddIntG.Wk.dv_pderiv_subst_coe
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:21:47.656029+00:00
-- url     : https://prove2.me/theorems/906b98f4-8cf3-5fa6-9d01-ed040c54fef2
-- title:
--   Wk: dv pderiv subst coe
-- statement:
--   The Wk construction uses the dv pderiv subst coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/DvCoeffMulEqZeroOfLtOrder.lean#L25-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/DvCoeffMulEqZeroOfLtOrder.lean#L25-L30

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

theorem PI.AddIntG.Wk.dv_pderiv_subst_coe {R : Type*} [CommRing R] {σ : Type*} {a : MvPowerSeries σ R}
    (ha : PowerSeries.HasSubst a) (P : Polynomial R) (i : σ) :
    MvPowerSeries.pderiv R i (PowerSeries.subst a (P : PowerSeries R)) =
      PowerSeries.subst a (PowerSeries.derivative R (P : PowerSeries R)) * MvPowerSeries.pderiv R i a := by sorry
