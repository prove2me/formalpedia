-- Prove2me | Theorems.Thm_PI_PC_log_two_pi_ge
-- name    : PI.PC.log_two_pi_ge
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:35:45.350062+00:00
-- url     : https://prove2.me/theorems/d400ff51-8b22-5f2c-9b43-309c551a31a0
-- title:
--   PC: log two pi ge
-- statement:
--   The PC construction uses the log two pi ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/LogFactorialLe.lean#L81-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/LogFactorialLe.lean#L81-L96

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

theorem PI.PC.log_two_pi_ge : (9 : ℝ) / 5 ≤ log (2 * π) := by sorry
