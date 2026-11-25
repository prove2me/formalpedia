-- Prove2me | Theorems.Thm_PI_OrbShared_ExpSum_coeff_X_add_X_pow
-- name    : PI.OrbShared.ExpSum.coeff_X_add_X_pow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:16:38.470516+00:00
-- url     : https://prove2.me/theorems/2ef1a1c4-49a1-42ea-bd4d-14381e00042c
-- title:
--   Exp Sum: coeff X add X pow
-- statement:
--   The Exp Sum construction uses the coeff X add X pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/ExpSum.lean#L25-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/ExpSum.lean#L25-L54

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

theorem PI.OrbShared.ExpSum.coeff_X_add_X_pow (n : ℕ) (e : Fin 2 →₀ ℕ) :
    coeff e ((X 0 + X 1 : MvPowerSeries (Fin 2) K) ^ n) =
      if e 0 + e 1 = n then (n.choose (e 0) : K) else 0 := by sorry
