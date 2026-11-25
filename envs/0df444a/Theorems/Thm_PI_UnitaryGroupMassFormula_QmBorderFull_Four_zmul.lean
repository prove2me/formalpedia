-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_Four_zmul
-- name    : PI.UnitaryGroupMassFormula.QmBorderFull.Four.zmul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:39:52.195811+00:00
-- url     : https://prove2.me/theorems/bdd6cfa2-a7ed-4012-b7ae-f694be2d917a
-- title:
--   Four: zmul
-- statement:
--   The Four construction uses the zmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderMinorRotation/SkipTwoSuccAboveComp.lean#L61-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderMinorRotation/SkipTwoSuccAboveComp.lean#L61-L62

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

theorem PI.UnitaryGroupMassFormula.QmBorderFull.Four.zmul {A : Type} [Ring A] (z : ℤ) (y : A) : (z : A) * y = z • y := by sorry
