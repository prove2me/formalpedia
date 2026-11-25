-- Prove2me | Theorems.Thm_PI_VolStabW_LocalCountingSum_cnt_summable
-- name    : PI.VolStabW.LocalCountingSum.cnt_summable
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:40:12.879074+00:00
-- url     : https://prove2.me/theorems/d6614535-22b8-5ccf-a188-a0486d02e257
-- title:
--   Local Counting Sum: cnt summable
-- statement:
--   The Local Counting Sum construction uses the cnt summable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensQ.lean#L42-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensQ.lean#L42-L50

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensQ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open NumberField IsDedekindDomain Filter Asymptotics
open scoped nonZeroDivisors
open PI.VolStabW.LocalCountingSum
variable (K : Type) [Field K] [NumberField K]

theorem PI.VolStabW.LocalCountingSum.cnt_summable : Summable fun n : ℕ ↦ cnt K n / (n : ℝ) ^ 2 := by sorry
