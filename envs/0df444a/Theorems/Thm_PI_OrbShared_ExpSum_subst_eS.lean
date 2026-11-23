-- Prove2me | Theorems.Thm_PI_OrbShared_ExpSum_subst_eS
-- name    : PI.OrbShared.ExpSum.subst_eS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:35:53.765796+00:00
-- url     : https://prove2.me/theorems/d20dd3d4-0068-41d9-941f-ecbc340824af
-- title:
--   Exp Sum: subst e S
-- statement:
--   The Exp Sum construction uses the subst e S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/ExpSum.lean#L170-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/ExpSum.lean#L170-L172

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

theorem PI.OrbShared.ExpSum.subst_eS {b : τ → MvPowerSeries υ K} (hb : HasSubst b) (f : MvPowerSeries τ K)
    (hf : constantCoeff f = 0) : subst b (eS f) = eS (subst b f) := by sorry
