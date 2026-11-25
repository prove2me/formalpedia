-- Prove2me | Theorems.Thm_PI_PC_lcmUpto_le_three_pow
-- name    : PI.PC.lcmUpto_le_three_pow
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:35:35.188772+00:00
-- url     : https://prove2.me/theorems/256bced7-91e2-4ff3-95ce-2d39e85b39fc
-- title:
--   PC: lcm Upto le three pow
-- statement:
--   The PC construction uses the lcm Upto le three pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/PsiUpperBoundOfLtThirtyMulSixPow.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/PsiUpperBoundOfLtThirtyMulSixPow.lean#L27-L28

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PsiUpperBoundOfLtThirtyMulSixPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PC
open Real

theorem PI.PC.lcmUpto_le_three_pow : ∀ n < 30, Nat.lcmUpto n ≤ 3 ^ n := by sorry
