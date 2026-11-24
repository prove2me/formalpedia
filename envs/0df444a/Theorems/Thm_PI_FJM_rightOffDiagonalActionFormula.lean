-- Prove2me | Theorems.Thm_PI_FJM_rightOffDiagonalActionFormula
-- name    : PI.FJM.rightOffDiagonalActionFormula
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:03.559339+00:00
-- url     : https://prove2.me/theorems/f797ae4a-ec5c-4b2c-a176-319f56757052
-- title:
--   FJM: right Off Diagonal Action Formula
-- statement:
--   The FJM construction uses the right Off Diagonal Action Formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L696-L697
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L696-L697

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
open PI PI.FJM

theorem PI.FJM.rightOffDiagonalActionFormula : FormRaise2 := by sorry
