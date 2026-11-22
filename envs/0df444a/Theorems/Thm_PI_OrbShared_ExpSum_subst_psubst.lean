-- Prove2me | Theorems.Thm_PI_OrbShared_ExpSum_subst_psubst
-- name    : PI.OrbShared.ExpSum.subst_psubst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:18:50.95122+00:00
-- url     : https://prove2.me/theorems/c069f425-cdae-42a9-ad02-a5605ae940de
-- title:
--   Exp Sum: subst psubst
-- statement:
--   The Exp Sum construction uses the subst psubst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/ExpSum.lean#L125-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/ExpSum.lean#L125-L129

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

theorem PI.OrbShared.ExpSum.subst_psubst {b : τ → MvPowerSeries υ K} (hb : HasSubst b) {a : MvPowerSeries τ K}
    (ha : PowerSeries.HasSubst a) (φ : PowerSeries K) :
    subst b (PowerSeries.subst a φ) = PowerSeries.subst (subst b a) φ := by sorry
