-- Prove2me | Theorems.Thm_PI_AddIntG_Wk_rt_Acf_ne
-- name    : PI.AddIntG.Wk.rt_Acf_ne
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:22:44.575124+00:00
-- url     : https://prove2.me/theorems/e4132273-671b-56bb-ae00-5e129418a533
-- title:
--   Wk: rt Acf ne
-- statement:
--   The Wk construction uses the rt Acf ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/ThirdRootSubVarZeroNeZero.lean#L113-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/ThirdRootSubVarZeroNeZero.lean#L113-L116

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffWSeriesVarZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_ThirdRootSubVarZeroNeZero
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

theorem PI.AddIntG.Wk.rt_Acf_ne (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    MvPowerSeries.constantCoeff (Acf W wq) ≠ 0 := by sorry
