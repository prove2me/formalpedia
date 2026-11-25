-- Prove2me | Theorems.Thm_P2M_PI_WGL_ioExists_of__3083dde9c611
-- name    : P2M_PI_WGL_ioExists_of__3083dde9c611
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T06:02:14.762364+00:00
-- url     : https://prove2.me/theorems/6b7e0471-77a4-4556-8ad5-e6dd8173aa7c
-- title:
--   P2 M PI WGL io Exists of  3083dde9c611: P2 M PI WGL io Exists of  3083dde9c611
-- statement:
--   The P2 M PI WGL io Exists of  3083dde9c611 construction uses the P2 M PI WGL io Exists of  3083dde9c611 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/IoXiHw.lean#L140-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/IoXiHw.lean#L140-L141

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_IoPolDiagHw
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_IoXiHw
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

theorem P2M_PI_WGL_ioExists_of__3083dde9c611 (h3 : PI.HwIrred) (h4 : PI.GTBranch) (hx : XiFacts) : IoExists := by sorry

alias «PI».«WGL».«ioExists_of'» := P2M_PI_WGL_ioExists_of__3083dde9c611
