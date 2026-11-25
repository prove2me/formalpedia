-- Prove2me | Theorems.Thm_PI_TailWork_w_nonneg
-- name    : PI.TailWork.w_nonneg
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:28:50.439597+00:00
-- url     : https://prove2.me/theorems/ba70782e-0d26-597a-8be9-8e3f786b9c75
-- title:
--   Tail Work: w nonneg
-- statement:
--   The Tail Work construction uses the w nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PrimeLogarithmTail/SumLogBlock.lean#L46-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PrimeLogarithmTail/SumLogBlock.lean#L46-L53

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

theorem PI.TailWork.w_nonneg (n : ℕ) (hn : 2 ≤ n) : 0 ≤ g n - g (n + 1) := by sorry
