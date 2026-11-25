-- Prove2me | Theorems.Thm_PI_Mk_trace_kron
-- name    : PI.Mk.trace_kron
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:34:49.103147+00:00
-- url     : https://prove2.me/theorems/6f7cac7f-daea-4b17-a907-2d8e9d5c442c
-- title:
--   Mk: trace kron
-- statement:
--   The Mk construction uses the trace kron property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinkowskiBound/PowerSum.lean#L59-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinkowskiBound/PowerSum.lean#L59-L64

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSumStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Mk
open Matrix Finset

theorem PI.Mk.trace_kron {n : Type*} [Fintype n] [DecidableEq n] (k : ℕ) (A : Matrix n n ℤ) :
    (kron k A).trace = A.trace ^ k := by sorry
