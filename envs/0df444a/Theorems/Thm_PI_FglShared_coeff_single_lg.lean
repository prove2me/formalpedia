-- Prove2me | Theorems.Thm_PI_FglShared_coeff_single_lg
-- name    : PI.FglShared.coeff_single_lg
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:30:12.208545+00:00
-- url     : https://prove2.me/theorems/bba6348a-e31e-4114-9199-00fd47925e8b
-- title:
--   Fgl Shared: coeff single lg
-- statement:
--   The Fgl Shared construction uses the coeff single lg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupCommon/CoeffSingleLg.lean#L51-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupCommon/CoeffSingleLg.lean#L51-L61

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

theorem PI.FglShared.coeff_single_lg {σ : Type} [DecidableEq σ] (l : PowerSeries ℂ_[p]) (i j : σ) {k : ℕ}
    (hk : k ≠ 0) : coeff (Finsupp.single i k) (PowerSeries.subst (X j : MvPowerSeries σ ℂ_[p]) l) =
      if j = i then PowerSeries.coeff k l else 0 := by sorry
