-- Prove2me | Theorems.Thm_PI_FglShared_eq_one_add_X_of_deriv
-- name    : PI.FglShared.eq_one_add_X_of_deriv
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:57.509211+00:00
-- url     : https://prove2.me/theorems/6c2556de-f87b-5cb4-b5a9-6e68d9861a33
-- title:
--   Fgl Shared: eq one add X of deriv
-- statement:
--   The Fgl Shared construction uses the eq one add X of deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupCommon/ExpLog.lean#L21-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupCommon/ExpLog.lean#L21-L36

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupCommon_ExpLog
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
variable {K : Type} [Field K] [CharZero K]

theorem PI.FglShared.eq_one_add_X_of_deriv {g : PowerSeries K}
    (hd : PowerSeries.derivative K g = g * (1 + PowerSeries.X)⁻¹)
    (h0 : PowerSeries.constantCoeff g = 1) : g = 1 + PowerSeries.X := by sorry
