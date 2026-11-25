-- Prove2me | Theorems.Thm_PI_AddIntG_Wk_constantCoeff_lam
-- name    : PI.AddIntG.Wk.constantCoeff_lam
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:22:54.867401+00:00
-- url     : https://prove2.me/theorems/5cbb0652-3472-4715-9f57-683300d730ce
-- title:
--   Wk: constant Coeff lam
-- statement:
--   The Wk construction uses the constant Coeff lam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/CoeffWSeriesVarZero.lean#L72-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/CoeffWSeriesVarZero.lean#L72-L74

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

theorem PI.AddIntG.Wk.constantCoeff_lam (wq : PowerSeries ℂ_[p]) : MvPowerSeries.constantCoeff (lam wq) = 0 := by sorry
