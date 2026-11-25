-- Prove2me | Theorems.Thm_PI_HookSteps_highest_weight_last_zero
-- name    : PI.HookSteps.highest_weight_last_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:07:24.561924+00:00
-- url     : https://prove2.me/theorems/4cface89-7dd6-41ba-8f1f-e1cd10c76cb9
-- title:
--   Hook Steps: highest weight last zero
-- statement:
--   The Hook Steps construction uses the highest weight last zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/HighestWeightLastZero.lean#L41-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/HighestWeightLastZero.lean#L41-L57

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShiftNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_HighestWeightLastZero
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

theorem PI.HookSteps.highest_weight_last_zero : HwLastZero := by sorry
