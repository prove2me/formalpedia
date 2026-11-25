-- Prove2me | Theorems.Thm_PI_OrbShared_ExpSum_eS_sum
-- name    : PI.OrbShared.ExpSum.eS_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:35:54.015484+00:00
-- url     : https://prove2.me/theorems/360842d2-d23b-49d0-94d4-91239cb5ba64
-- title:
--   Exp Sum: e S sum
-- statement:
--   The Exp Sum construction uses the e S sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/ExpSum.lean#L153-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/ExpSum.lean#L153-L168

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

theorem PI.OrbShared.ExpSum.eS_sum {ι : Type*} (s : Finset ι) (f : ι → MvPowerSeries τ K)
    (hf : ∀ i ∈ s, constantCoeff (f i) = 0) : eS (∑ i ∈ s, f i) = ∏ i ∈ s, eS (f i) := by sorry
