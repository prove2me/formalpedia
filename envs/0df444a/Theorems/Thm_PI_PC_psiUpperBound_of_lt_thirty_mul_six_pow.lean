-- Prove2me | Theorems.Thm_PI_PC_psiUpperBound_of_lt_thirty_mul_six_pow
-- name    : PI.PC.psiUpperBound_of_lt_thirty_mul_six_pow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:35:55.200434+00:00
-- url     : https://prove2.me/theorems/7e686bcf-1b12-5539-b3ef-320f0b3dfc9b
-- title:
--   PC: psi Upper Bound of lt thirty mul six pow
-- statement:
--   The PC construction uses the psi Upper Bound of lt thirty mul six pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/PsiUpperBoundOfLtThirtyMulSixPow.lean#L45-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/PsiUpperBoundOfLtThirtyMulSixPow.lean#L45-L76

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

theorem PI.PC.psiUpperBound_of_lt_thirty_mul_six_pow (hA : ANum) (hD : DUpper) (hS : Sandwich) (k : ℕ) :
    ∀ x : ℝ, 1 ≤ x → x < 30 * 6 ^ k → Chebyshev.psi x ≤ 1.1056 * x + 0.7 * (log x) ^ 2 := by sorry
