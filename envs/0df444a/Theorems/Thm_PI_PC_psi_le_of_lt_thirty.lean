-- Prove2me | Theorems.Thm_PI_PC_psi_le_of_lt_thirty
-- name    : PI.PC.psi_le_of_lt_thirty
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:35:49.404651+00:00
-- url     : https://prove2.me/theorems/1ba77ff4-4cb3-4545-9b69-96eb711e08c5
-- title:
--   PC: psi le of lt thirty
-- statement:
--   The PC construction uses the psi le of lt thirty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/PsiUpperBoundOfLtThirtyMulSixPow.lean#L30-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/PsiUpperBoundOfLtThirtyMulSixPow.lean#L30-L43

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

theorem PI.PC.psi_le_of_lt_thirty {x : ℝ} (h0 : 0 ≤ x) (hx : x < 30) : Chebyshev.psi x ≤ 1.1056 * x := by sorry
