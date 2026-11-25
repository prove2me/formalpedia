-- Prove2me | Theorems.Thm_PI_FglShared_int_of_mul_eq_one
-- name    : PI.FglShared.int_of_mul_eq_one
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:30:35.545486+00:00
-- url     : https://prove2.me/theorems/7a8bb994-e793-4f13-8d4b-111287457388
-- title:
--   Fgl Shared: int of mul eq one
-- statement:
--   The Fgl Shared construction uses the int of mul eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupCommon/ExpLog.lean#L124-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupCommon/ExpLog.lean#L124-L158

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

theorem PI.FglShared.int_of_mul_eq_one {σ : Type} [DecidableEq σ] {u n : MvPowerSeries σ ℂ_[p]}
    (hn : ∀ α, ‖coeff α n‖ ≤ 1) (hn0 : constantCoeff n = 1) (h : u * n = 1) :
    ∀ α, ‖coeff α u‖ ≤ 1 := by sorry
