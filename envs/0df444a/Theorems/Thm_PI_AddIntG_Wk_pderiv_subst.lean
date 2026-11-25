-- Prove2me | Theorems.Thm_PI_AddIntG_Wk_pderiv_subst
-- name    : PI.AddIntG.Wk.pderiv_subst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:15:25.305951+00:00
-- url     : https://prove2.me/theorems/c00bc49d-e6de-4176-a257-96fd834df761
-- title:
--   Wk: pderiv subst
-- statement:
--   The Wk construction uses the pderiv subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/DvCoeffMulEqZeroOfLtOrder.lean#L32-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/DvCoeffMulEqZeroOfLtOrder.lean#L32-L62

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

theorem PI.AddIntG.Wk.pderiv_subst {R : Type*} [CommRing R] {σ : Type*} {a : MvPowerSeries σ R}
    (ha : PowerSeries.HasSubst a) (f : PowerSeries R) (i : σ) :
    MvPowerSeries.pderiv R i (PowerSeries.subst a f) =
      PowerSeries.subst a (PowerSeries.derivative R f) * MvPowerSeries.pderiv R i a := by sorry
