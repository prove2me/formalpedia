-- Prove2me | Theorems.Thm_PI_PC_third_le_log
-- name    : PI.PC.third_le_log
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:35:52.820315+00:00
-- url     : https://prove2.me/theorems/40e966fa-8f15-4fff-b984-c9c12be7c213
-- title:
--   PC: third le log
-- statement:
--   The PC construction uses the third le log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/LogFactorialLe.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/LogFactorialLe.lean#L28-L31

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

theorem PI.PC.third_le_log : (1 : ℝ) / 3 ≤ log (3 / 2) := by sorry
