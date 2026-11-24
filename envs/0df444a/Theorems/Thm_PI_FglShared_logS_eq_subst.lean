-- Prove2me | Theorems.Thm_PI_FglShared_logS_eq_subst
-- name    : PI.FglShared.logS_eq_subst
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:32:14.30734+00:00
-- url     : https://prove2.me/theorems/8384aafc-c053-4165-9306-b5efa46acbb9
-- title:
--   Fgl Shared: log S eq subst
-- statement:
--   The Fgl Shared construction uses the log S eq subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupCommon/ExpLog.lean#L82-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupCommon/ExpLog.lean#L82-L103

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
variable {p : ℕ} [Fact p.Prime]

theorem PI.FglShared.logS_eq_subst {σ : Type} {F : MvPowerSeries σ ℂ_[p]} (hF : constantCoeff F = 1) :
    logS F = PowerSeries.subst (F - 1) (PowerSeries.log ℂ_[p]) := by sorry
