-- Prove2me | Theorems.Thm_PI_OrbShared_ExpSum_coeff_exp_K
-- name    : PI.OrbShared.ExpSum.coeff_exp_K
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:35:36.903243+00:00
-- url     : https://prove2.me/theorems/1252a8d6-1628-4756-bd50-3d5fab525011
-- title:
--   Exp Sum: coeff exp K
-- statement:
--   The Exp Sum construction uses the coeff exp K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/ExpSum.lean#L56-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/ExpSum.lean#L56-L57

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

theorem PI.OrbShared.ExpSum.coeff_exp_K (n : ℕ) : PowerSeries.coeff n (PowerSeries.exp K) = ((n.factorial : K))⁻¹ := by sorry
