-- Prove2me | Theorems.Thm_PI_WGL_gTLower_of
-- name    : PI.WGL.gTLower_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:59.35314+00:00
-- url     : https://prove2.me/theorems/755a6c1d-c847-4632-ac2a-f18c79b05d8e
-- title:
--   WGL: g TLower of
-- statement:
--   The WGL construction uses the g TLower of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/GTLowerOf.lean#L14-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/GTLowerOf.lean#L14-L22

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_Assembly
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ConstructionNum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ConstructionXi
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ConstructionIo
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_Capelli2_2
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ConstructionLift
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ConstructionAdj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ConstructionBrInt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_GTLowerOf
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

theorem PI.WGL.gTLower_of (h2 : Formalism.BasicNotions.FactDelDualNabla) (h3 : PI.HwIrred) (h4 : PI.GTBranch)
    (h5 : PI.SchurFock) : PI.GTLower := by sorry
