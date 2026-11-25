-- Prove2me | Theorems.Thm_PI_Mk_trace_idem_nat
-- name    : PI.Mk.trace_idem_nat
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:34:48.370688+00:00
-- url     : https://prove2.me/theorems/9f6e8191-7f73-4686-8853-2d61ee805eca
-- title:
--   Mk: trace idem nat
-- statement:
--   The Mk construction uses the trace idem nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinkowskiBound/PowerSum.lean#L8-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinkowskiBound/PowerSum.lean#L8-L15

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

theorem PI.Mk.trace_idem_nat {n : Type*} [Fintype n] [DecidableEq n] (E : Matrix n n ℚ) (hE : E * E = E) :
    ∃ r : ℕ, E.trace = (r : ℚ) := by sorry
