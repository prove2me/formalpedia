-- Prove2me | Theorems.Thm_PI_TailWork_w_mul
-- name    : PI.TailWork.w_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:29:10.452639+00:00
-- url     : https://prove2.me/theorems/4615c9a0-fbe6-4319-b448-d662273d57be
-- title:
--   Tail Work: w mul
-- statement:
--   The Tail Work construction uses the w mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PrimeLogarithmTail/SumLogBlock.lean#L55-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PrimeLogarithmTail/SumLogBlock.lean#L55-L64

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

theorem PI.TailWork.w_mul (n : ℕ) (hn : 2 ≤ n) : (g n - g (n + 1)) * (n : ℝ) = h n - h (n + 1) := by sorry
