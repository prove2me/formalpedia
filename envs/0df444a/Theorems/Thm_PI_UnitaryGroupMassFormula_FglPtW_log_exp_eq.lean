-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_FglPtW_log_exp_eq
-- name    : PI.UnitaryGroupMassFormula.FglPtW.log_exp_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:38:31.199499+00:00
-- url     : https://prove2.me/theorems/c86e78ed-69ff-530d-987e-ce036b0210de
-- title:
--   Fgl Pt W: log exp eq
-- statement:
--   The Fgl Pt W construction uses the log exp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupPoints/ConstantCoeffLogEqZero.lean#L24-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupPoints/ConstantCoeffLogEqZero.lean#L24-L30

import Definitions.Def_Formalism_PeriodIntegrals_FglPtW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupPoints_ConstantCoeffLogEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FglPtW
open PI.FglPtW

theorem PI.UnitaryGroupMassFormula.FglPtW.log_exp_eq {K : Type} [CommRing K] {l ex : PowerSeries K}
    (h0 : PowerSeries.constantCoeff ex = 0) (hlex : PowerSeries.subst ex l = PowerSeries.X)
    {σ : Type} (y : MvPowerSeries σ K) (hy : MvPowerSeries.constantCoeff y = 0) :
    PowerSeries.subst (PowerSeries.subst y ex) l = y := by sorry
