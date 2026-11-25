-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_Four_sign_two_succAbove_left
-- name    : PI.UnitaryGroupMassFormula.QmBorderFull.Four.sign_two_succAbove_left
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:39:43.355926+00:00
-- url     : https://prove2.me/theorems/c3794e0a-6445-44f5-a3ff-254399d1b3dd
-- title:
--   Four: sign two succ Above left
-- statement:
--   The Four construction uses the sign two succ Above left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderMinorRotation/SkipTwoSuccAboveComp.lean#L128-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderMinorRotation/SkipTwoSuccAboveComp.lean#L128-L137

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_SkipTwoSuccAboveComp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmBorderFull PI.UnitaryGroupMassFormula.QmBorderFull.Four
open PI

theorem PI.UnitaryGroupMassFormula.QmBorderFull.Four.sign_two_succAbove_left {k : ℕ} (x : Fin (k + 1)) (y : Fin k) :
    sg2 (x.succAbove y) x = -(-1 : ℤ) ^ ((x : ℕ) + (y : ℕ)) := by sorry
