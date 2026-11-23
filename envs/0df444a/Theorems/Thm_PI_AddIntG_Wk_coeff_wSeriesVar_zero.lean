-- Prove2me | Theorems.Thm_PI_AddIntG_Wk_coeff_wSeriesVar_zero
-- name    : PI.AddIntG.Wk.coeff_wSeriesVar_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:15:06.730409+00:00
-- url     : https://prove2.me/theorems/71561d74-c316-4125-bf43-1070fa61a0bb
-- title:
--   Wk: coeff w Series Var zero
-- statement:
--   The Wk construction uses the coeff w Series Var zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/CoeffWSeriesVarZero.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/CoeffWSeriesVarZero.lean#L28-L31

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffPowMemS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffWSeriesVarZero
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

theorem PI.AddIntG.Wk.coeff_wSeriesVar_zero (wq : PowerSeries ℂ_[p]) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (wv wq 0) = if e 1 = 0 then PowerSeries.coeff (e 0) (wser wq) else 0 := by sorry
