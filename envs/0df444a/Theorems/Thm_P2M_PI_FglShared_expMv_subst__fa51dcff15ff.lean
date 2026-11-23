-- Prove2me | Theorems.Thm_P2M_PI_FglShared_expMv_subst__fa51dcff15ff
-- name    : P2M_PI_FglShared_expMv_subst__fa51dcff15ff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:11:40.667895+00:00
-- url     : https://prove2.me/theorems/38ef2704-eaee-4163-8d96-a7adba094ea0
-- title:
--   P2 M PI Fgl Shared exp Mv subst  fa51dcff15ff: P2 M PI Fgl Shared exp Mv subst  fa51dcff15ff
-- statement:
--   The P2 M PI Fgl Shared exp Mv subst  fa51dcff15ff construction uses the P2 M PI Fgl Shared exp Mv subst  fa51dcff15ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupCommon/ExpLog.lean#L116-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupCommon/ExpLog.lean#L116-L122

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

theorem P2M_PI_FglShared_expMv_subst__fa51dcff15ff {σ : Type} {x : MvPowerSeries σ ℂ_[p]} (hx : constantCoeff x = 0)
    {f : PowerSeries ℂ_[p]} (hf : MvPowerSeries.constantCoeff f = 0) :
    PI.FglPhSplit.expMv (PowerSeries.subst x f) = PowerSeries.subst x (PI.FglPhSplit.expMv f) := by sorry

alias «PI».«FglShared».«expMv_subst'» := P2M_PI_FglShared_expMv_subst__fa51dcff15ff
