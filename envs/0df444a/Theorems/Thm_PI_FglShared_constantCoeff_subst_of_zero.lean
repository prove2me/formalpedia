-- Prove2me | Theorems.Thm_PI_FglShared_constantCoeff_subst_of_zero
-- name    : PI.FglShared.constantCoeff_subst_of_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:46:22.033797+00:00
-- url     : https://prove2.me/theorems/96e92f4d-a14f-4097-a3c3-4549134c54fa
-- title:
--   Fgl Shared: constant Coeff subst of zero
-- statement:
--   The Fgl Shared construction uses the constant Coeff subst of zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupCommon/ExpLog.lean#L13-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupCommon/ExpLog.lean#L13-L19

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

theorem PI.FglShared.constantCoeff_subst_of_zero {τ : Type} {a : MvPowerSeries τ K} (ha : constantCoeff a = 0)
    (f : PowerSeries K) : constantCoeff (PowerSeries.subst a f) = PowerSeries.constantCoeff f := by sorry
