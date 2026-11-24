-- Prove2me | Theorems.Thm_PI_WFJM_leftOffDiagonalActionFormula
-- name    : PI.WFJM.leftOffDiagonalActionFormula
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:26.524503+00:00
-- url     : https://prove2.me/theorems/13193bec-d9de-4c13-93bd-11c13c1016d6
-- title:
--   WFJM: left Off Diagonal Action Formula
-- statement:
--   The WFJM construction uses the left Off Diagonal Action Formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L154-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L154-L159

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

theorem PI.WFJM.leftOffDiagonalActionFormula : FormRaise1 := by sorry
