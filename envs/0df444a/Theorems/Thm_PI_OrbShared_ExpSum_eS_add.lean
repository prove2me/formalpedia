-- Prove2me | Theorems.Thm_PI_OrbShared_ExpSum_eS_add
-- name    : PI.OrbShared.ExpSum.eS_add
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:16:35.261454+00:00
-- url     : https://prove2.me/theorems/8e97a1e1-6d68-552c-88c2-5f51efe855a8
-- title:
--   Exp Sum: e S add
-- statement:
--   The Exp Sum construction uses the e S add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/ExpSum.lean#L131-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/ExpSum.lean#L131-L144

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

theorem PI.OrbShared.ExpSum.eS_add (f g : MvPowerSeries τ K) (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    eS (f + g) = eS f * eS g := by sorry
