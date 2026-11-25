-- Prove2me | Theorems.Thm_PI_HookSteps_polE_mul_X
-- name    : PI.HookSteps.polE_mul_X
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:17:53.051129+00:00
-- url     : https://prove2.me/theorems/6f2dc48a-890e-44f9-9886-a8a18ddbde21
-- title:
--   Hook Steps: pol E mul X
-- statement:
--   The Hook Steps construction uses the pol E mul X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/DetShift.lean#L39-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/DetShift.lean#L39-L54

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShiftNormOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LGradedLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockqLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open PI PI.HookSteps
variable {N : ℕ}

theorem PI.HookSteps.polE_mul_X (a b : Fin N) (p : MvPolynomial (Fin N × Fin N) ℚ) (v : Fin N × Fin N) :
    polE N a b (p * X v) = polE N a b p * X v + p * (if v.1 = b then X (a, v.2) else 0) := by sorry
