-- Prove2me | Theorems.Thm_PI_HookSteps_Qn_last_zero
-- name    : PI.HookSteps.Qn_last_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:09:34.838803+00:00
-- url     : https://prove2.me/theorems/aad46335-bf1e-4d4f-b128-92585696e60d
-- title:
--   Hook Steps: Qn last zero
-- statement:
--   The Hook Steps construction uses the Qn last zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/HookNorm.lean#L50-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/HookNorm.lean#L50-L63

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShiftNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_HookNorm
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

theorem PI.HookSteps.Qn_last_zero (n : ℕ) (ν : Fin (n + 1) → ℕ) (h : ν (Fin.last n) = 0) :
    Qn ν = (∏ i : Fin n, (ν (Fin.castSucc i) + (n - i))) * Qn (fun i : Fin n => ν (Fin.castSucc i)) := by sorry
