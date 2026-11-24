-- Prove2me | Theorems.Thm_PI_WFJM_rightOffDiagonalActionFormula
-- name    : PI.WFJM.rightOffDiagonalActionFormula
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:34.187932+00:00
-- url     : https://prove2.me/theorems/2d84e477-b51a-4250-a1cf-b096c188413d
-- title:
--   WFJM: right Off Diagonal Action Formula
-- statement:
--   The WFJM construction uses the right Off Diagonal Action Formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L161-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L161-L166

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.WFJM
open MvPolynomial
open PI.FJM

theorem PI.WFJM.rightOffDiagonalActionFormula : FormRaise2 := by sorry
