-- Prove2me | Theorems.Thm_PI_OrbShared_ExpSum_rename_eS
-- name    : PI.OrbShared.ExpSum.rename_eS
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:47:09.9887+00:00
-- url     : https://prove2.me/theorems/74b1c65d-1ff1-468a-9eab-73ecc010e9df
-- title:
--   Exp Sum: rename e S
-- statement:
--   The Exp Sum construction uses the rename e S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/ExpSum.lean#L174-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/ExpSum.lean#L174-L177

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

theorem PI.OrbShared.ExpSum.rename_eS (e : τ → υ) [Filter.TendstoCofinite e] (f : MvPowerSeries τ K) (hf : constantCoeff f = 0) :
    rename e (eS f) = eS (rename e f) := by sorry
