-- Prove2me | Theorems.Thm_PI_OrbShared_ExpSum_eS_zero
-- name    : PI.OrbShared.ExpSum.eS_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:16:47.544556+00:00
-- url     : https://prove2.me/theorems/c0785a3a-0f85-4198-9ca2-edc1e0009f7f
-- title:
--   Exp Sum: e S zero
-- statement:
--   The Exp Sum construction uses the e S zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/ExpSum.lean#L146-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/ExpSum.lean#L146-L151

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OrbitPowerSeriesCoefficients_ExpSum
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
open PI PI.OrbShared PI.OrbShared.ExpSum
open MvPowerSeries
variable {K : Type*} [Field K] [CharZero K]
variable {τ υ : Type*}

theorem PI.OrbShared.ExpSum.eS_zero : eS (0 : MvPowerSeries τ K) = 1 := by sorry
