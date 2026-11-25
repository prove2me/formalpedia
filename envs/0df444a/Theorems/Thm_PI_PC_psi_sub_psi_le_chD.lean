-- Prove2me | Theorems.Thm_PI_PC_psi_sub_psi_le_chD
-- name    : PI.PC.psi_sub_psi_le_chD
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:36:07.074353+00:00
-- url     : https://prove2.me/theorems/89d21486-8698-407b-931a-8a817feeb056
-- title:
--   PC: psi sub psi le ch D
-- statement:
--   The PC construction uses the psi sub psi le ch D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/LogFactorialEqSumOfLe.lean#L123-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/LogFactorialEqSumOfLe.lean#L123-L142

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_LogFactorialEqSumOfLe
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
open ArithmeticFunction hiding log id
open scoped Nat Chebyshev ArithmeticFunction.zeta

theorem PI.PC.psi_sub_psi_le_chD (x : ℝ) : ψ x - ψ (x / 6) ≤ chD x := by sorry
