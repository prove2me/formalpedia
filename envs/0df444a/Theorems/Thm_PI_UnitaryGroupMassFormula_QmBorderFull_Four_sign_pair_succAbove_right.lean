-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_Four_sign_pair_succAbove_right
-- name    : PI.UnitaryGroupMassFormula.QmBorderFull.Four.sign_pair_succAbove_right
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:39:50.165803+00:00
-- url     : https://prove2.me/theorems/96db1ee1-addb-43b0-8b4f-95c12cbf5000
-- title:
--   Four: sign pair succ Above right
-- statement:
--   The Four construction uses the sign pair succ Above right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderMinorRotation/SkipTwoSuccAboveComp.lean#L118-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderMinorRotation/SkipTwoSuccAboveComp.lean#L118-L126

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

theorem PI.UnitaryGroupMassFormula.QmBorderFull.Four.sign_pair_succAbove_right {k : ℕ} (w : Fin (k + 1)) (j : Fin k) :
    sg2 w (w.succAbove j) = (-1 : ℤ) ^ ((w : ℕ) + (j : ℕ)) := by sorry
