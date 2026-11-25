-- Prove2me | Theorems.Thm_PI_TailWork_log_four_lt
-- name    : PI.TailWork.log_four_lt
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:28:39.01592+00:00
-- url     : https://prove2.me/theorems/a6c3c981-c59e-427a-a416-f0f246e29adf
-- title:
--   Tail Work: log four lt
-- statement:
--   The Tail Work construction uses the log four lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PrimeLogarithmTail/SumLogBlock.lean#L127-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PrimeLogarithmTail/SumLogBlock.lean#L127-L134

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PrimeLogarithmTail_SumLogBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.TailWork
open Finset

theorem PI.TailWork.log_four_lt : Real.log 4 < 1.3863 := by sorry
