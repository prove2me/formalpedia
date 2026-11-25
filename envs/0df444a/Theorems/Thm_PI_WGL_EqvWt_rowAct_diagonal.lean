-- Prove2me | Theorems.Thm_PI_WGL_EqvWt_rowAct_diagonal
-- name    : PI.WGL.EqvWt.rowAct_diagonal
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:45:20.317185+00:00
-- url     : https://prove2.me/theorems/e7496d85-57ea-438b-9d50-11d71af2954a
-- title:
--   Eqv Wt: row Act diagonal
-- statement:
--   The Eqv Wt construction uses the row Act diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftEqvWt.lean#L27-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftEqvWt.lean#L27-L36

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftEqvWt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open PI.WGL.EqvWt

theorem PI.WGL.EqvWt.rowAct_diagonal {r c : ℕ} (d : Fin r → ℂ) :
    rowAct ℂ (n := c) (Matrix.diagonal d) = aeval (fun v : Fin r × Fin c => C (d v.1) * X v) := by sorry
