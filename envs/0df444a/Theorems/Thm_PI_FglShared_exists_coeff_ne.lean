-- Prove2me | Theorems.Thm_PI_FglShared_exists_coeff_ne
-- name    : PI.FglShared.exists_coeff_ne
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:02.286122+00:00
-- url     : https://prove2.me/theorems/49e623d8-b673-4672-9033-b8d918fb3ed3
-- title:
--   Fgl Shared: exists coeff ne
-- statement:
--   The Fgl Shared construction uses the exists coeff ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupCommon/CoeffSingleLg.lean#L32-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupCommon/CoeffSingleLg.lean#L32-L41

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

theorem PI.FglShared.exists_coeff_ne {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (hinv : PowerSeries.subst ex l = PowerSeries.X) : ∃ k, k ≠ 0 ∧ PowerSeries.coeff k l ≠ 0 := by sorry
