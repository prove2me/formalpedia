-- Prove2me | Theorems.Thm_PI_FglShared_l_constantCoeff
-- name    : PI.FglShared.l_constantCoeff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:48:54.221123+00:00
-- url     : https://prove2.me/theorems/a69e6ab3-93a8-4556-bfa9-447a3e48d83d
-- title:
--   Fgl Shared: l constant Coeff
-- statement:
--   The Fgl Shared construction uses the l constant Coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupCommon/CoeffSingleLg.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupCommon/CoeffSingleLg.lean#L11-L16

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupCommon_ExpLog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupCommon_CoeffSingleLg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FglShared
open MvPowerSeries
variable {p : ℕ} [Fact p.Prime]

theorem PI.FglShared.l_constantCoeff {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (hinv : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.constantCoeff l = 0 := by sorry
