-- Prove2me | Theorems.Thm_PI_OrbShared_ExpSum_eS_X_add_X
-- name    : PI.OrbShared.ExpSum.eS_X_add_X
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:16:40.238799+00:00
-- url     : https://prove2.me/theorems/791d446c-f41b-49b7-8905-a19102482d0c
-- title:
--   Exp Sum: e S X add X
-- statement:
--   The Exp Sum construction uses the e S X add X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/ExpSum.lean#L81-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/ExpSum.lean#L81-L121

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

theorem PI.OrbShared.ExpSum.eS_X_add_X : eS (X 0 + X 1 : MvPowerSeries (Fin 2) K) = eS (X 0) * eS (X 1) := by sorry
