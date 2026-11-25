-- Prove2me | Theorems.Thm_PI_HookSteps_Pn_last_zero
-- name    : PI.HookSteps.Pn_last_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:07:37.796104+00:00
-- url     : https://prove2.me/theorems/b340784c-1923-5402-951d-9e655842c56d
-- title:
--   Hook Steps: Pn last zero
-- statement:
--   The Hook Steps construction uses the Pn last zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/HookNorm.lean#L38-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/HookNorm.lean#L38-L48

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

theorem PI.HookSteps.Pn_last_zero (n : ℕ) (ν : Fin (n + 1) → ℕ) (h : ν (Fin.last n) = 0) :
    Pn ν = Pn (fun i : Fin n => ν (Fin.castSucc i)) * ∏ i : Fin n, (ν (Fin.castSucc i) + (n - i)) := by sorry
