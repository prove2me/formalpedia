-- Prove2me | Theorems.Thm_PI_WGL_LTE_sg_detShift
-- name    : PI.WGL.LTE.sg_detShift
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:47:22.720808+00:00
-- url     : https://prove2.me/theorems/65d28c2e-a537-49f6-b3ce-eebee1de5500
-- title:
--   LTE: sg det Shift
-- statement:
--   The LTE construction uses the sg det Shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleE.lean#L112-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleE.lean#L112-L115

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.LTE
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM PI.WGL.LTC PI.WGL.LTD

theorem PI.WGL.LTE.sg_detShift {n : ℕ} (sg : DomWeight n) (hn : 0 < n) :
    sg.detShift = sg.w ⟨n - 1, by omega⟩ := by sorry
