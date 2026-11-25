-- Prove2me | Theorems.Thm_PI_WGL_LTB_natW_add
-- name    : PI.WGL.LTB.natW_add
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:45:08.053059+00:00
-- url     : https://prove2.me/theorems/cf5bf737-0c53-45a7-934d-5e20bae87fb0
-- title:
--   LTB: nat W add
-- statement:
--   The LTB construction uses the nat W add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleB.lean#L258-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleB.lean#L258-L266

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleM
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.LTB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTM

theorem PI.WGL.LTB.natW_add {n : ℕ} (sg : DomWeight n) (i : Fin n) : ((sg.natW i : ℕ) : ℤ) + sg.detShift = sg.w i := by sorry
