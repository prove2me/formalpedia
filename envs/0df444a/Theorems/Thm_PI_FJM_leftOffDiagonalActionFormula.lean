-- Prove2me | Theorems.Thm_PI_FJM_leftOffDiagonalActionFormula
-- name    : PI.FJM.leftOffDiagonalActionFormula
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:43.744816+00:00
-- url     : https://prove2.me/theorems/a4c46be3-9570-4247-9100-48afd4eaef0c
-- title:
--   FJM: left Off Diagonal Action Formula
-- statement:
--   The FJM construction uses the left Off Diagonal Action Formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L694-L695
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L694-L695

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

theorem PI.FJM.leftOffDiagonalActionFormula : FormRaise1 := by sorry
