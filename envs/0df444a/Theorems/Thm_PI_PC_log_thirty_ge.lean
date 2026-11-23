-- Prove2me | Theorems.Thm_PI_PC_log_thirty_ge
-- name    : PI.PC.log_thirty_ge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:35:54.937892+00:00
-- url     : https://prove2.me/theorems/0bd98184-c911-4965-8db4-33c4e273c73e
-- title:
--   PC: log thirty ge
-- statement:
--   The PC construction uses the log thirty ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/LogFactorialLe.lean#L98-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/LogFactorialLe.lean#L98-L121

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_LogFactorialLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.PC
open Finset Real
open scoped Nat

theorem PI.PC.log_thirty_ge : (33 : ℝ) / 10 ≤ log 30 := by sorry
