-- Prove2me | Theorems.Thm_PI_FglShared_constantCoeff_logS
-- name    : PI.FglShared.constantCoeff_logS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:46:29.716535+00:00
-- url     : https://prove2.me/theorems/91c92fe4-3437-44c3-8f01-43609377cf68
-- title:
--   Fgl Shared: constant Coeff log S
-- statement:
--   The Fgl Shared construction uses the constant Coeff log S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupCommon/ExpLog.lean#L74-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupCommon/ExpLog.lean#L74-L76

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

theorem PI.FglShared.constantCoeff_logS {σ : Type} (F : MvPowerSeries σ ℂ_[p]) : constantCoeff (logS F) = 0 := by sorry
