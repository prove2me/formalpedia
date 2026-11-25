-- Prove2me | Theorems.Thm_PI_PC_psiLowerBound_holds
-- name    : PI.PC.psiLowerBound_holds
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:36:09.928105+00:00
-- url     : https://prove2.me/theorems/61851eee-1955-43e2-942d-d5a4b3e330bd
-- title:
--   PC: psi Lower Bound holds
-- statement:
--   The PC construction uses the psi Lower Bound holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/PsiLowerBoundHolds.lean#L11-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/PsiLowerBoundHolds.lean#L11-L11

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_LogFactorialEqSumOfLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_LogFactorialLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PsiUpperBoundOfLtThirtyMulSixPow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PsiLowerBoundHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PC

theorem PI.PC.psiLowerBound_holds : CHLower := by sorry
